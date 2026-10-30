#!/usr/bin/env python3
"""
References:
  [CI-11] https://craftinginterpreters.com/resolving-and-binding.html
  [CI-10] https://craftinginterpreters.com/functions.html
  [CI-9] https://craftinginterpreters.com/control-flow.html
  [CI-8] https://craftinginterpreters.com/statements-and-state.html
  [CI-7] https://craftinginterpreters.com/evaluating-expressions.html
  [CI-6] https://craftinginterpreters.com/parsing-expressions.html
  [TUT-LOL] https://www.tutorialspoint.com/lolcode/index.htm
  [CORNELL] https://www.cs.cornell.edu/courses/cs4120/2022sp/notes/semantic/
  [WIKI-SA] https://en.wikipedia.org/wiki/Semantic_analysis_(compilers)
  [WIKIBK] https://en.wikibooks.org/wiki/Compiler_Construction/Semantic_Analysis
  [UC3M] https://ocw.uc3m.es/pluginfile.php/1848/mod_page/content/12/contents_unit7.pdf
  [RUSTC] https://rust.googlesource.com/rust/+/08650fbb506c44fbc95d91abfb7cd95a56bbff30/compiler/rustc_mir_dataflow/src/framework/lattice.rs
  [ROCKS] https://docs.rs/rocks-lang
  [OWN] from own module
===================================================================================
"""
import math
import re
import sys
from typing import Any, Callable, Dict, List, NamedTuple, Optional, Set, Tuple

from lol_lexemes import (
    Token, tokenize_file, tokenize_source,
    CLASS_LITERAL, CLASS_TYPE_LITERAL, CLASS_VAR_IDENT, CLASS_FUNC_IDENT,
    CLASS_LOOP_IDENT, CLASS_COMMENT, CLASS_STRING_DELIMITER,
)

# --------------------------------------------------------------------------- types
NOOB, NUMBR, NUMBAR, YARN, TROOF, ANY = "NOOB", "NUMBR", "NUMBAR", "YARN", "TROOF", "ANY"
# ANY = "statically unknown". LOLCODE is dynamically typed ([PROJ] DATA TYPES, [TUT-LOL] Types),
# so ANY never produces a type error. Role of ANY = "top" of the type lattice ([RUSTC]).

ARITH = {"SUM OF", "DIFF OF", "PRODUKT OF", "QUOSHUNT OF", "MOD OF", "BIGGR OF", "SMALLR OF"}
BOOL2 = {"BOTH OF", "EITHER OF", "WON OF"}
COMPARE = {"BOTH SAEM", "DIFFRINT"}
INFINITE = {"ALL OF", "ANY OF"}
STRUCTURAL = {"YA RLY", "NO WAI", "MEBBE", "OIC", "OMG", "OMGWTF",
              "IM OUTTA YR", "IF U SAY SO", "BUHBYE", "KTHXBYE"}


class Val(NamedTuple):
    """Static info about an expression: inferred type + constant value if known.
    Sources: [CORNELL] (type attached to each expression), [OWN] (the const field)."""
    type: str
    const: Any = None


class Issue(NamedTuple):
    """One diagnostic. Sources: [CORNELL] (lexical / syntax / semantic error categories),
    [LEX] (LexError.__str__ format reused)."""
    line: int
    severity: str   # "error" | "warning"
    category: str   # "Lexical" | "Syntax" | "Semantic"
    message: str

    def __str__(self) -> str:
        return f"{self.category} {self.severity} (line {self.line}): {self.message}"


class SyntaxProblem(Exception):
    """Aborts the current line only, so later lines are still checked.
    Sources: [CI-6] 6.3 (report syntax errors and keep going), [ROCKS] (continue after error)."""


class RuntimeProblem(Exception):
    """Aborts runtime execution when a dynamic operation fails (e.g. bad cast, divide by zero)."""
    def __init__(self, line: int, message: str):
        super().__init__(message)
        self.line = line
        self.message = message


class _BreakSignal(Exception):
    """Control-flow signal raised by GTFO at runtime."""


class _ReturnSignal(Exception):
    """Control-flow signal raised by FOUND YR at runtime."""
    def __init__(self, val: Val):
        self.val = val


MAX_LOOP_ITERATIONS = 100_000
MAX_CALL_DEPTH = 500


def _unescape_yarn(raw: str) -> str:
    """Decode LOLCODE 1.2 YARN escape sequences (:), :>, :o, :\", ::)."""
    escapes = {')': '\n', '>': '\t', 'o': '\a', '"': '"', ':': ':'}
    out: List[str] = []
    i, n = 0, len(raw)
    while i < n:
        if raw[i] == ":" and i + 1 < n and raw[i + 1] in escapes:
            out.append(escapes[raw[i + 1]])
            i += 2
        else:
            out.append(raw[i])
            i += 1
    return "".join(out)


class Symbol:
    """Symbol-table entry. `ready` is False between declaring a variable and finishing its
    initializer. Sources: [CI-11] 11.3.2 (declare/define split), [WIKIBK] (entry holds type info)."""
    def __init__(self, name: str, typ: str, line: int, initialized: bool, is_param=False, value: Any = None):
        self.name, self.type, self.line = name, typ, line
        self.initialized, self.is_param = initialized, is_param
        self.value = value
        self.used = is_param
        self.ready = True

    def __repr__(self) -> str:
        return f"Symbol(name={self.name!r}, type={self.type!r}, value={self.value!r}, line={self.line})"


class FuncInfo(NamedTuple):
    """Function signature. Sources: [PROJ] FUNCTIONS (fixed parameter count), [GRAM] function_def."""
    name: str
    params: List[str]
    line: int


class Frame:
    """An open block (TOP / IF / SWITCH / LOOP / FUNC) on the nesting stack.
    Sources: [CI-11] 11.3 (scopes behave like a stack), [CORNELL] (push on entry, pop on exit)."""
    def __init__(self, kind: str, line: int, label: str = ""):
        self.kind, self.line, self.label = kind, line, label
        self.snapshot: Dict[str, str] = {}
        self.branch_ends: List[Dict[str, str]] = []
        self.seen: Set[str] = set()
        self.cases: Set[Tuple[str, Any]] = set()
        self.dead = False
        self.dead_warned = False


class Cursor:
    """Lookahead helper over one line's tokens. Source: [CI-6] 6.2 (the peek/match/consume
    helpers every recursive-descent parser uses)."""
    def __init__(self, toks: List[Token]):
        self.t, self.i = toks, 0

    def peek(self, k: int = 0) -> Optional[Token]:
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def next(self) -> Token:
        tok = self.peek()
        if tok is None:
            raise SyntaxProblem("unexpected end of line")
        self.i += 1
        return tok

    def at_end(self) -> bool:
        return self.i >= len(self.t)

    def match(self, keyword: str) -> bool:
        if kw(self.peek()) == keyword:
            self.i += 1
            return True
        return False

    def expect_kw(self, keyword: str, ctx: str = "") -> Token:
        tok = self.peek()
        if kw(tok) != keyword:
            got = repr(tok.lexeme) if tok else "end of line"
            raise SyntaxProblem(f"expected {keyword!r}{ctx} but found {got}")
        return self.next()

    def expect_class(self, cls: str, what: str) -> Token:
        tok = self.peek()
        if tok is None or tok.classification != cls:
            got = repr(tok.lexeme) if tok else "end of line"
            raise SyntaxProblem(f"expected {what} but found {got}")
        return self.next()

    def expect_end(self) -> None:
        if not self.at_end():
            raise SyntaxProblem(f"unexpected extra token {self.peek().lexeme!r}")


_NON_KEYWORD = {CLASS_LITERAL, CLASS_TYPE_LITERAL, CLASS_VAR_IDENT, CLASS_FUNC_IDENT, CLASS_LOOP_IDENT}


def kw(tok: Optional[Token]) -> Optional[str]:
    """Keyword text with whitespace normalised ('I  HAS A' -> 'I HAS A'); None for literals and
    identifiers. Sources: [LEX] keyword_regex (allows [ \\t]+ between words), [TUT-LOL] Syntax & Spacing
    ('multiple spaces and tabs are treated as single spaces')."""
    if tok is None or tok.classification in _NON_KEYWORD:
        return None
    return " ".join(tok.lexeme.split())


# --------------------------------------------------------------------------- analyzer
class SemanticAnalyzer:
    def __init__(self, tokens: List[Token],
                 input_fn: Callable[[], str] = input,
                 output_fn: Callable[[str], None] = print):
        """Group tokens by source line and drop comments.
        Sources: [PROJ] SPACING ('each statement is delimited by the new line') and COMMENTS
        (comments are ignored), [TUT-LOL] Syntax & Spacing (newline ends a command), [LEX] Token.line."""
        self.lines: List[Tuple[int, List[Token]]] = []
        for t in tokens:
            if t.classification == CLASS_COMMENT:
                continue
            if self.lines and self.lines[-1][0] == t.line:
                self.lines[-1][1].append(t)
            else:
                self.lines.append((t.line, [t]))
        self.input_fn = input_fn
        self.output_fn = output_fn
        self.issues: List[Issue] = []
        self.functions: Dict[str, FuncInfo] = {}
        it_sym = Symbol("IT", NOOB, 0, True, value=None)
        it_sym.used = False
        self.globals: Dict[str, Symbol] = {"IT": it_sym}
        self.scope = self.globals
        self.in_function = False
        self.phase = "PRE"            # PRE (before HAI) -> BODY -> DECL (in WAZZUP) -> BODY -> POST
        self.frames: List[Frame] = [Frame("TOP", 0)]
        self.it_set = False
        self._saved_it_set = False
        self._func_ranges: Dict[str, Tuple[int, int]] = {}
        self._call_depth = 0
        self.seen_hai = self.seen_kthxbye = self.seen_wazzup = False
        self.body_started = self.pre_reported = False
        self.first_line = self.lines[0][0] if self.lines else 1
        self.last_line = self.lines[-1][0] if self.lines else 1

    @property
    def it_type(self) -> str:
        return self.scope["IT"].type

    @it_type.setter
    def it_type(self, typ: str) -> None:
        self.scope["IT"].type = typ

    # ------------------------------------------------------------ reporting
    def err(self, line: int, msg: str, cat: str = "Semantic") -> None:
        """Record an error. Sources: [CI-11] 11.5 (resolution errors are reported, not thrown, so
        analysis continues), [CORNELL] (error categories)."""
        self.issues.append(Issue(line, "error", cat, msg))

    def warn(self, line: int, msg: str) -> None:
        """Record a warning. Source: [CI-11] 11.5 ('report warnings for code that isn't necessarily
        wrong but probably isn't useful ... unreachable code ... variable never read')."""
        self.issues.append(Issue(line, "warning", "Semantic", msg))

    # ------------------------------------------------------------ driver
    def analyze(self, execute: bool = True) -> List[Issue]:
        """Run the two passes over the program.
        Sources: [CI-11] 11.2.1 (a separate pass after parsing, before execution),
        [WIKI-SA] (declared-before-use / types can't be checked by the grammar, so they need
        this extra phase), [PROJ] FUNCTIONS (a call may precede its definition, so signatures
        are collected first). Per-line recovery: [CI-6] 6.3, [ROCKS]."""
        self._collect_functions()
        for idx, (line, toks) in enumerate(self.lines):
            try:
                self._statement(idx, line, toks)
            except SyntaxProblem as e:
                self.err(line, str(e), "Syntax")
        self._finish()
        if execute and not any(i.severity == "error" for i in self.issues):
            self._execute()
        self.issues.sort(key=lambda i: (i.line, i.severity != "error"))
        return self.issues

    def _collect_functions(self) -> None:
        """Pass 1: build the function table; reject duplicate function names.
        Sources: [PROJ] FILE NAMING (functions may sit before HAI / after KTHXBYE) and FUNCTIONS,
        [GRAM] function_def / function_name, [CI-11] 11.3.5 (function names are declared in the
        surrounding scope), [WIKIBK] (global symbol table)."""
        for line, toks in self.lines:
            if kw(toks[0]) != "HOW IZ I":
                continue
            try:
                cur = Cursor(toks)
                cur.next()
                name = cur.expect_class(CLASS_FUNC_IDENT, "a function name after HOW IZ I").lexeme
                params = self._params(cur)
            except SyntaxProblem as e:
                self.err(line, str(e), "Syntax")
                continue
            if name in self.functions:
                self.err(line, f"function '{name}' is already defined on line {self.functions[name].line}")
            else:
                self.functions[name] = FuncInfo(name, params, line)

    def _params(self, cur: Cursor) -> List[str]:
        """Parse `[YR p1 [AN YR p2 ...]]`; the lexer fuses 'AN YR' into one token.
        Sources: [PROJ] FUNCTIONS - Definition, [TUT-LOL] Functions - Definition,
        [GRAM] param_list, [LEX] ('AN YR' Parameter Keyword)."""
        params: List[str] = []
        if cur.match("YR"):
            params.append(cur.expect_class(CLASS_VAR_IDENT, "a parameter name").lexeme)
            while cur.match("AN YR"):
                params.append(cur.expect_class(CLASS_VAR_IDENT, "a parameter name").lexeme)
        cur.expect_end()
        return params

    # ------------------------------------------------------------ symbol table helpers
    def _lookup(self, name: str, line: int, mark_used: bool = True) -> Optional[Symbol]:
        """Resolve a variable in the CURRENT scope only (IT is implicit).
        Sources: [PROJ] VARIABLES (must be declared; implicit IT) and FUNCTIONS ('cannot access
        identifiers outside of it'), [TUT-LOL] Variables - Scope ('no global scope'; IT is local),
        [CI-11] 11.1 (a use refers to the preceding declaration) and 11.3.3 (error when a
        variable is read in its own initializer), [CORNELL] (lookup in the symbol table),
        [UC3M] (scope checking)."""
        if name == "IT":
            return self.scope["IT"]
        sym = self.scope.get(name)
        if sym is None:
            if self.in_function and name in self.globals:
                self.err(line, f"function cannot access outer variable '{name}'; pass it as a parameter (YR {name})")
            else:
                self.err(line, f"variable '{name}' is used before being declared")
            return None
        if not sym.ready:
            self.err(line, f"variable '{name}' cannot be read in its own initializer")
            return None
        if mark_used:
            sym.used = True
        return sym

    def _snapshot(self) -> Dict[str, str]:
        """Copy of every variable's static type (plus IT) at a control-flow point.
        Sources: [RUSTC] (a dataflow state per program point), [CI-11] 11.2.1 (analysis walks the
        tree without executing it)."""
        snap = {n: s.type for n, s in self.scope.items()}
        snap["IT"] = self.it_type
        return snap

    def _restore(self, snap: Dict[str, str]) -> None:
        """Reset types to a snapshot (start of another branch). Source: [RUSTC] (each path starts from
        the state at the branch point), [OWN]."""
        for n, t in snap.items():
            if n in self.scope:
                self.scope[n].type = t
                if t == ANY:
                    self.scope[n].value = None

    def _merge(self, snaps: List[Dict[str, str]]) -> None:
        """Join point: keep a type only if every path agrees, otherwise ANY.
        Sources: [RUSTC] FlatSet::join (equal elements stay, different elements go to top),
        [CI-11] 11.3.6 (a static analysis is conservative: it considers every branch that could
        run), [PROJ] DATA TYPES (dynamic typing)."""
        keys: Set[str] = set()
        for s in snaps:
            keys |= set(s)
        merged = {k: (snaps[0].get(k, ANY) if len({s.get(k, ANY) for s in snaps}) == 1 else ANY) for k in keys}
        self._restore(merged)

    def _weaken_to(self, snap: Dict[str, str]) -> None:
        """Join the current state with an earlier snapshot (loop exit, switch fall-through).
        Sources: [RUSTC] join, [TUT-LOL] Decision Making - Case (fall-through into the next OMG), [OWN]."""
        self._merge([self._snapshot(), snap])

    # ------------------------------------------------------------ expressions
    def _expr(self, cur: Cursor, line: int, nested: bool = False) -> Val:
        """Parse one prefix-notation expression and return its static type.
        Sources: [PROJ] OPERATIONS (prefix notation, binary ops, AN required, SMOOSH/ALL OF/ANY OF
        cannot be nested), [GRAM] expression, [CI-6] 6.2 (recursive descent: one function call
        per grammar alternative), [CORNELL] (type checking is a recursive traversal that
        synthesises a type for each expression)."""
        t = cur.peek()
        if t is None:
            raise SyntaxProblem("expected an expression but reached end of line")
        k = kw(t)
        if t.classification == CLASS_STRING_DELIMITER:
            return self._yarn(cur)
        if t.classification == CLASS_LITERAL:
            cur.next()
            return self._literal_val(t)
        if t.classification == CLASS_VAR_IDENT:
            cur.next()
            sym = self._lookup(t.lexeme, line)
            return Val(sym.type if sym else ANY)
        if k in ARITH:
            cur.next()
            a, b = self._binary(cur, k, line)
            return self._arith(k, a, b, line)
        if k in BOOL2:
            cur.next()
            self._binary(cur, k, line)
            return Val(TROOF)
        if k == "NOT":
            cur.next()
            self._expr(cur, line, nested=True)
            return Val(TROOF)
        if k in COMPARE:
            cur.next()
            a, b = self._binary(cur, k, line)
            self._check_compare(k, a, b, line)
            return Val(TROOF)
        if k in INFINITE:
            cur.next()
            if nested:
                self.err(line, f"{k} cannot be nested inside another operation")
            self._expr_list(cur, line, k, need_mkay=True)
            return Val(TROOF)
        if k == "SMOOSH":
            cur.next()
            if nested:
                self.err(line, "SMOOSH cannot be nested inside another operation")
            self._expr_list(cur, line, k, need_mkay=False)
            return Val(YARN)
        if k == "MAEK":
            cur.next()
            v = self._expr(cur, line, nested=True)
            cur.match("A")  # optional: [GRAM] cast_expr, [TUT-LOL] Typecasting ('[A]')
            tt = cur.expect_class(CLASS_TYPE_LITERAL, "a type (NUMBR, NUMBAR, YARN, TROOF, NOOB) after MAEK")
            self._check_cast(v, tt.lexeme, line)
            return Val(tt.lexeme)
        if k == "I IZ":
            return self._call(cur, line)
        raise SyntaxProblem(f"unexpected {t.lexeme!r} where an expression was expected")

    def _literal_val(self, t: Token) -> Val:
        """Literal token -> Val. Sources: [LEX] Token.subtype (NUMBR/NUMBAR/TROOF),
        [PROJ] DATA TYPES, [TUT-LOL] Data Types."""
        if t.subtype == "NUMBR":
            return Val(NUMBR, int(t.lexeme))
        if t.subtype == "NUMBAR":
            return Val(NUMBAR, float(t.lexeme))
        if t.subtype == "TROOF":
            return Val(TROOF, t.lexeme == "WIN")
        raise SyntaxProblem(f"unexpected literal {t.lexeme!r}")

    def _yarn(self, cur: Cursor) -> Val:
        """YARN = open-quote, content, close-quote tokens.
        Sources: [LEX] _scan_yarn (String Delimiter / Literal(YARN) / String Delimiter),
        [GRAM] literal, [TUT-LOL] Strings."""
        cur.next()
        content = cur.expect_class(CLASS_LITERAL, "string contents")
        cur.expect_class(CLASS_STRING_DELIMITER, "a closing quote")
        return Val(YARN, _unescape_yarn(content.lexeme))

    def _binary(self, cur: Cursor, op: str, line: int) -> Tuple[Val, Val]:
        """`OP x AN y`. Sources: [PROJ] OPERATIONS ('The AN keyword is required to separate
        operands'; [TUT-LOL] makes AN optional, [PROJ] wins), [GRAM] arithmetic/boolean/comparison."""
        a = self._expr(cur, line, nested=True)
        if not cur.match("AN"):
            raise SyntaxProblem(f"{op} needs 'AN' between its two operands")
        b = self._expr(cur, line, nested=True)
        return a, b

    def _expr_list(self, cur: Cursor, line: int, op: str, need_mkay: bool) -> List[Val]:
        """Variable-arity operand list. Sources: [PROJ] Concatenation/Boolean Operations (SMOOSH has
        no MKAY; ALL OF / ANY OF need MKAY -- [TUT-LOL] would also let end-of-line close them,
        [PROJ] is stricter), [GRAM] expr_list."""
        vals = [self._expr(cur, line, nested=True)]
        while cur.match("AN"):
            vals.append(self._expr(cur, line, nested=True))
        if need_mkay and not cur.match("MKAY"):
            raise SyntaxProblem(f"{op} must be closed with MKAY")
        return vals

    def _num_kind(self, v: Val, op: str, line: int) -> str:
        """Can this operand be implicitly cast to a number, and to which kind?
        Sources: [PROJ] Arithmetic ('if a value cannot be typecast, the operation must fail') and
        Typecasting, [TUT-LOL] Data Types - Untyped (math on NOOB is an error) and Math (a YARN is read
        as NUMBAR if it has a '.', else NUMBR; non-numeric characters are an error), [UC3M]
        (type conversions on operands)."""
        if v.type in (NUMBR, NUMBAR):
            return v.type
        if v.type == TROOF:
            return NUMBR
        if v.type == NOOB:
            self.err(line, f"{op}: a NOOB (untyped/uninitialized) value cannot be implicitly cast to a number")
            return ANY
        if v.type == YARN and v.const is not None:
            s = v.const
            if s == "" or any(c not in "0123456789-." for c in s):
                self.err(line, f"{op}: YARN \"{s}\" cannot be cast to a number")
                return ANY
            if not re.fullmatch(r"-?[0-9]+(\.[0-9]+)?", s):
                self.err(line, f"{op}: YARN \"{s}\" is not a well-formed number")
                return ANY
            return NUMBAR if "." in s else NUMBR
        return ANY

    def _arith(self, op: str, a: Val, b: Val, line: int) -> Val:
        """Result type of an arithmetic op, plus a constant divide-by-zero check.
        Sources: [PROJ] Arithmetic (two NUMBRs -> NUMBR, any NUMBAR -> NUMBAR), [TUT-LOL] Operators
        (same rule), [UC3M] (int + real widens to real). Divide-by-zero check: [OWN]."""
        ka, kb = self._num_kind(a, op, line), self._num_kind(b, op, line)
        if op in ("QUOSHUNT OF", "MOD OF"):
            z = self._const_num(b)
            if z is not None and z == 0:
                self.err(line, f"{op}: division by constant zero")
        if NUMBAR in (ka, kb):
            return Val(NUMBAR)
        if ka == NUMBR and kb == NUMBR:
            return Val(NUMBR)
        return Val(ANY)

    @staticmethod
    def _const_num(v: Val) -> Optional[float]:
        """Numeric value of a constant operand, if known. Source: [OWN]; WIN/FAIL -> 1/0 per
        [TUT-LOL] Operators."""
        try:
            if v.type in (NUMBR, NUMBAR):
                return float(v.const)
            if v.type == TROOF and v.const is not None:
                return 1.0 if v.const else 0.0
            if v.type == YARN and v.const is not None:
                return float(v.const)
        except (TypeError, ValueError):
            pass
        return None

    def _check_compare(self, op: str, a: Val, b: Val, line: int) -> None:
        """Warn when operand types are known, differ, and are not both numeric.
        Sources: [PROJ] Comparison ('no automatic typecasting'), [TUT-LOL] Comparison Operators (integer math
        for two NUMBRs, floating point if either is a NUMBAR, otherwise no casting, so
        `BOTH SAEM "3" AN 3` is FAIL). NUMBR-vs-NUMBAR is therefore legal and not warned."""
        numeric = {NUMBR, NUMBAR}
        if ANY in (a.type, b.type) or a.type == b.type or {a.type, b.type} <= numeric:
            return
        always = "FAIL" if op == "BOTH SAEM" else "WIN"
        self.warn(line, f"{op} compares {a.type} with {b.type}; no implicit cast is done, so it is always {always}")

    def _check_cast(self, v: Val, target: str, line: int) -> None:
        """Validate an explicit cast of a known constant.
        Sources: [PROJ] Typecasting (YARN -> number only if no non-numeric characters; explicit
        NOOB cast allowed), [TUT-LOL] Data Types - Untyped."""
        if target in (NUMBR, NUMBAR) and v.type == YARN and v.const is not None:
            s = v.const
            if s == "" or any(c not in "0123456789-." for c in s):
                self.err(line, f"cannot cast YARN \"{s}\" to {target}")

    def _call(self, cur: Cursor, line: int) -> Val:
        """`I IZ name [YR e1 [AN YR e2 ...]] MKAY` -- function must exist, arity must match.
        Sources: [PROJ] FUNCTIONS - Calling, [GRAM] function_call / arg_list, [LEX] ('I IZ' and
        'AN YR' tokens, Function Identifier), [TUT-LOL] Functions - Calling ('the arity is
        determined in the definition'), [CI-11] 11.3 (visitCallExpr resolves the callee and every
        argument)."""
        cur.next()
        name = cur.expect_class(CLASS_FUNC_IDENT, "a function name after I IZ").lexeme
        argc = 0
        if cur.match("YR"):
            self._expr(cur, line)
            argc = 1
            while cur.match("AN YR"):
                self._expr(cur, line)
                argc += 1
        if not cur.match("MKAY"):
            raise SyntaxProblem(f"call to '{name}' must be closed with MKAY")
        fn = self.functions.get(name)
        if fn is None:
            self.err(line, f"call to undefined function '{name}'")
        elif len(fn.params) != argc:
            self.err(line, f"function '{name}' takes {len(fn.params)} argument(s) but {argc} were given")
        return Val(ANY)  # return type unknown: a function may return any type

    # ------------------------------------------------------------ statements
    def _statement(self, idx: int, line: int, toks: List[Token]) -> None:
        """Dispatch one statement line.
        Sources: [GRAM] statement alternatives, [PROJ] STATEMENTS / FILE NAMING / VARIABLES,
        [CI-11] 11.3 (one visit method per statement kind), 11.5 (context checks such as
        return-only-in-function and break-only-in-loop are done by tracking where we are)."""
        cur = Cursor(toks)
        k = kw(toks[0])
        top = self.frames[-1]

        # ---- program-frame phase checks ([PROJ] FILE NAMING, VARIABLES; phase machine is [OWN])
        if not self.in_function and k not in ("HOW IZ I", "IF U SAY SO"):
            if self.phase == "PRE" and k != "HAI":
                if not self.pre_reported:
                    self.err(line, "program must start with HAI (only comments or functions may precede it)")
                    self.pre_reported = True
                self.phase = "BODY"
            elif self.phase == "POST":
                self.err(line, "nothing but comments or functions may follow KTHXBYE")
                return
            elif self.phase == "DECL" and k not in ("I HAS A", "BUHBYE"):
                self.err(line, "only variable declarations (I HAS A) are allowed inside WAZZUP ... BUHBYE")
            if self.phase == "BODY" and k not in ("HAI", "WAZZUP"):
                self.body_started = True

        # ---- block-shape checks ([PROJ] IF-THEN / SWITCH-CASE; unreachable code: [CI-11] 11.5)
        if k not in STRUCTURAL:
            if top.kind == "IF" and "ya" not in top.seen:
                self.err(line, "O RLY? must be followed by YA RLY before any statement")
            if top.kind == "SWITCH" and "case" not in top.seen:
                self.err(line, "WTF? must be followed by OMG <literal> before any statement")
            if top.dead and not top.dead_warned:
                self.warn(line, "unreachable statement (follows GTFO/FOUND YR in the same block)")
                top.dead_warned = True

        # ---- dispatch
        if k == "HAI":
            return self._hai(cur, line)
        if k == "KTHXBYE":
            return self._kthxbye(cur, line)
        if k == "WAZZUP":
            return self._wazzup(cur, line)
        if k == "BUHBYE":
            return self._buhbye(cur, line)
        if k == "I HAS A":
            return self._declare(cur, line)
        if k == "VISIBLE": #https://www.tutorialspoint.com/lolcode/lolcode_syntax.htm   Based on this a space as concat in strings is ok
            cur.next()
            self._expr(cur, line)
            while not cur.at_end():
                cur.match("AN")  # tolerated; [GRAM] print_args has no separator, [TUT-LOL] allows optional AN
                self._expr(cur, line)
            return
        if k == "GIMMEH":
            cur.next()
            v = cur.expect_class(CLASS_VAR_IDENT, "a variable after GIMMEH")
            cur.expect_end()
            sym = self._lookup(v.lexeme, line, mark_used=False)
            if sym:
                sym.type, sym.value, sym.initialized = YARN, None, True   # [PROJ] I/O + [TUT-LOL] Input/Output: input is a YARN
            return
        if k == "O RLY?":
            return self._o_rly(cur, line)
        if k in ("YA RLY", "NO WAI", "MEBBE"):
            return self._if_branch(cur, line, k)
        if k == "WTF?":
            return self._wtf(cur, line)
        if k in ("OMG", "OMGWTF"):
            return self._case(cur, line, k)
        if k == "OIC":
            return self._oic(cur, line)
        if k == "GTFO":
            cur.next(); cur.expect_end()
            # [PROJ]/[TUT-LOL]: GTFO breaks out of a switch / loop, or returns from a function;
            # [CI-11] 11.5 / [UC3M] flow-of-control check (break only where one can happen)
            if not (self.in_function or any(f.kind in ("LOOP", "SWITCH") for f in self.frames)):
                self.err(line, "GTFO is only valid inside a loop, a switch-case, or a function")
            top.dead = True
            return
        if k == "IM IN YR":
            return self._loop_start(cur, line, idx)
        if k == "IM OUTTA YR":
            return self._loop_end(cur, line)
        if k == "HOW IZ I":
            return self._func_start(cur, line)
        if k == "IF U SAY SO":
            return self._func_end(cur, line)
        if k == "FOUND YR":
            cur.next()
            if not self.in_function:   # [CI-11] 11.5.1 'invalid return' check
                self.err(line, "FOUND YR is only valid inside a function")
            self._expr(cur, line)
            cur.expect_end()
            top.dead = True
            return
        first = toks[0]
        if first.classification == CLASS_VAR_IDENT and kw(cur.peek(1)) == "R":
            return self._assign(cur, line)
        if first.classification == CLASS_VAR_IDENT and kw(cur.peek(1)) == "IS NOW A":
            return self._recast(cur, line)
        # bare expression -> value goes to IT.  Sources: [PROJ] Expression Statements, [TUT-LOL] same
        if (first.classification in (CLASS_LITERAL, CLASS_STRING_DELIMITER, CLASS_VAR_IDENT)
                or k in ARITH | BOOL2 | COMPARE | INFINITE | {"NOT", "SMOOSH", "MAEK", "I IZ"}):
            v = self._expr(cur, line)
            cur.expect_end()
            self.scope["IT"].type, self.scope["IT"].value, self.it_set = v.type, v.const, True
            return
        raise SyntaxProblem(f"unexpected {first.lexeme!r} at the start of a statement")

    # ---- program frame ------------------------------------------------------
    def _hai(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] FILE NAMING (start with HAI; version number not needed), [TUT-LOL] Program
        Structure (HAI may be followed by a version), [GRAM] program."""
        cur.next()
        if self.in_function:
            self.err(line, "HAI cannot appear inside a function")
        elif self.seen_hai:
            self.err(line, "duplicate HAI")
        self.seen_hai = True
        if self.phase == "PRE":
            self.phase = "BODY"
        t = cur.peek()
        if t is not None and t.classification == CLASS_LITERAL and t.subtype in ("NUMBR", "NUMBAR"):
            cur.next()
        cur.expect_end()

    def _kthxbye(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] FILE NAMING (end with KTHXBYE), [TUT-LOL] Program Structure (KTHXBYE closes
        the HAI block), [GRAM] program. Reporting still-open blocks: [OWN]."""
        cur.next(); cur.expect_end()
        if self.in_function:
            self.err(line, "KTHXBYE cannot appear inside a function (missing IF U SAY SO?)")
            return
        if self.seen_kthxbye:
            self.err(line, "duplicate KTHXBYE")
        if self.phase == "DECL":
            self.err(line, "WAZZUP block was never closed with BUHBYE")
        for f in self.frames[1:]:
            self.err(f.line, f"{self._open_name(f)} opened here is never closed")
        self.frames = self.frames[:1]
        self.seen_kthxbye, self.phase = True, "POST"

    def _wazzup(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] VARIABLES (WAZZUP at the beginning of the program, after HAI),
        [GRAM] program_block."""
        cur.next(); cur.expect_end()
        if self.in_function:
            self.err(line, "WAZZUP cannot appear inside a function")
        elif self.seen_wazzup:
            self.err(line, "duplicate WAZZUP block")
        elif self.body_started:
            self.err(line, "WAZZUP must come directly after HAI, before any other statement")
        elif self.phase == "BODY":
            self.phase = "DECL"
        self.seen_wazzup = True

    def _buhbye(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] VARIABLES, [GRAM] program_block."""
        cur.next(); cur.expect_end()
        if self.phase != "DECL":
            self.err(line, "BUHBYE without a matching WAZZUP")
        else:
            self.phase = "BODY"

    # ---- variables ----------------------------------------------------------
    def _declare(self, cur: Cursor, line: int) -> None:
        """`I HAS A x [ITZ expr]`: redeclaration, location, self-reference, initializer type.
        Sources: [PROJ] VARIABLES (I HAS A / ITZ; declarations only inside WAZZUP; initializer may
        be a literal, variable or expression; uninitialized = NOOB), [GRAM] declaration,
        [CI-11] 11.3.2 (declare the name first, evaluate the initializer, then mark it defined)
        and 11.5 ('Already a variable with this name in this scope'), [CORNELL] (insert into
        the symbol table on declaration). Local declarations inside functions are allowed: [OWN]
        ([PROJ] only mentions WAZZUP for the main program)."""
        cur.next()
        name = cur.expect_class(CLASS_VAR_IDENT, "a variable name after I HAS A").lexeme
        sym: Optional[Symbol] = None
        if name == "IT":
            self.err(line, "IT is the implicit variable and cannot be declared")
        elif name in self.scope:
            self.err(line, f"variable '{name}' is already declared on line {self.scope[name].line}")
        else:
            if name in self.functions:
                self.warn(line, f"variable '{name}' has the same name as a function")
            sym = Symbol(name, NOOB, line, False)
            sym.ready = False                  # declared, not yet defined  [CI-11] 11.3.2
            self.scope[name] = sym
        if not self.in_function and self.phase != "DECL":
            self.err(line, f"variable '{name}' must be declared inside the WAZZUP ... BUHBYE block")
        val: Optional[Val] = None
        try:
            if cur.match("ITZ"):
                val = self._expr(cur, line)
            cur.expect_end()
        finally:
            if sym is not None:
                sym.ready = True               # now defined
                if val is not None:
                    sym.type, sym.value, sym.initialized = val.type, val.const, True

    def _assign(self, cur: Cursor, line: int) -> None:
        """`x R expr`: target must exist; its static type becomes the expression's type.
        Sources: [PROJ] Assignment Statements, [TUT-LOL] Variables (no side effect on IT)
        and Declaration and Assignment (assigning changes the type), [GRAM] value_assignment,
        [CI-11] 11.3.4 (resolve the value first, then the assigned variable)."""
        name = cur.next().lexeme
        cur.next()
        sym = self._lookup(name, line, mark_used=False)
        v = self._expr(cur, line)
        cur.expect_end()
        if sym:
            sym.type, sym.value, sym.initialized = v.type, v.const, True

    def _recast(self, cur: Cursor, line: int) -> None:
        """`x IS NOW A TYPE`: target must exist; its type changes.
        Sources: [PROJ] Typecasting (re-casting via IS NOW A), [TUT-LOL] Typecasting (equivalent to
        `x R MAEK x A TYPE`), [GRAM] recast."""
        name = cur.next().lexeme
        cur.next()
        tt = cur.expect_class(CLASS_TYPE_LITERAL, "a type after IS NOW A")
        cur.expect_end()
        sym = self._lookup(name, line, mark_used=False)
        if sym:
            sym.type = tt.lexeme
            if tt.lexeme == NOOB:
                sym.value = None

    # ---- if / switch --------------------------------------------------------
    def _push(self, kind: str, line: int, label: str = "") -> Frame:
        """Open a block frame with a snapshot of the current types.
        Sources: [CI-11] 11.3.1 (blocks begin a scope that behaves like a stack), [CORNELL]
        (push on scope entry)."""
        f = Frame(kind, line, label)
        f.snapshot = self._snapshot()
        self.frames.append(f)
        return f

    def _o_rly(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] IF-THEN (O RLY? tests IT; alone on its line), [TUT-LOL] Decision Making,
        [GRAM] if_then. Warning when IT was never set: [OWN]."""
        cur.next(); cur.expect_end()
        if not self.it_set:
            self.warn(line, "O RLY? tests IT, but no expression has been evaluated before it (IT is NOOB -> FAIL)")
        self._push("IF", line)

    def _if_branch(self, cur: Cursor, line: int, k: str) -> None:
        """YA RLY / MEBBE / NO WAI order and per-branch type state.
        Sources: [PROJ] IF-THEN (YA RLY starts the if-clause, NO WAI the else, MEBBE has an
        expression on the same line), [TUT-LOL] Decision Making (YA RLY ... [MEBBE ...] [NO WAI ...] OIC),
        [GRAM] if_then / mebbe_clause / else_clause, [CI-11] 11.3.6 (analyse every branch,
        start each from the state before the branch)."""
        cur.next()
        top = self.frames[-1]
        if top.kind != "IF":
            self.err(line, f"{k} appears outside an O RLY? block")
            if k == "MEBBE":
                self._expr(cur, line)
            return
        if k == "YA RLY":
            if "ya" in top.seen:
                self.err(line, "duplicate YA RLY")
            top.seen.add("ya")
            cur.expect_end()
        else:
            if "ya" not in top.seen:
                self.err(line, f"{k} before YA RLY")
            if "nowai" in top.seen:
                self.err(line, f"{k} after NO WAI (NO WAI must be the last clause)")
            top.branch_ends.append(self._snapshot())
            self._restore(top.snapshot)
            if k == "MEBBE":
                v = self._expr(cur, line)
                self.it_type, self.it_set = v.type, True
                cur.expect_end()
            else:
                top.seen.add("nowai")
                cur.expect_end()
        top.dead = top.dead_warned = False

    def _wtf(self, cur: Cursor, line: int) -> None:
        """Sources: [PROJ] SWITCH-CASE (WTF? compares the value in IT), [TUT-LOL] Decision Making, [GRAM]
        switch_case."""
        cur.next(); cur.expect_end()
        if not self.it_set:
            self.warn(line, "WTF? switches on IT, but no expression has been evaluated before it")
        f = self._push("SWITCH", line)
        f.label = self.it_type   # remember IT's type for case checking [OWN]

    def _case(self, cur: Cursor, line: int, k: str) -> None:
        """OMG <literal> / OMGWTF: literals only, no duplicates, default last.
        Sources: [PROJ] SWITCH-CASE (cases are literals; OMGWTF is the default), [TUT-LOL] Decision Making
        ('must be a literal, not an expression ... Each literal must be unique'), [GRAM] case /
        default_case. Default-must-be-last and never-matches warning: [OWN] / [PROJ] ('Execution
        then stops when an OIC is encountered')."""
        cur.next()
        top = self.frames[-1]
        if top.kind != "SWITCH":
            self.err(line, f"{k} appears outside a WTF? block")
            if k == "OMG" and not cur.at_end():
                try:
                    self._case_literal(cur)
                except SyntaxProblem:
                    pass
            return
        self._weaken_to(top.snapshot)   # fall-through / skipped cases
        top.dead = top.dead_warned = False
        if "default" in top.seen:
            self.err(line, f"{k} after OMGWTF; the default case must be last")
        if k == "OMGWTF":
            cur.expect_end()
            top.seen.add("default")
            return
        top.seen.add("case")
        lit = self._case_literal(cur)
        cur.expect_end()
        key = (lit.type, lit.const)
        if key in top.cases:
            self.err(line, f"duplicate case literal {lit.const!r}")
        top.cases.add(key)
        if top.label in (NUMBR, NUMBAR, YARN, TROOF, NOOB) and top.label != lit.type and \
                {top.label, lit.type} - {NUMBR, NUMBAR}:
            self.warn(line, f"case is {lit.type} but IT is {top.label}; no implicit cast, so this case never matches")

    def _case_literal(self, cur: Cursor) -> Val:
        """Parse a literal-only operand. Sources: [PROJ] SWITCH-CASE ('OMG <value literal>'),
        [TUT-LOL] Decision Making ('must be a literal, not an expression')."""
        t = cur.peek()
        if t is not None and t.classification == CLASS_STRING_DELIMITER:
            return self._yarn(cur)
        if t is not None and t.classification == CLASS_LITERAL:
            cur.next()
            return self._literal_val(t)
        raise SyntaxProblem("OMG must be followed by a literal (NUMBR, NUMBAR, YARN or TROOF)")

    def _oic(self, cur: Cursor, line: int) -> None:
        """Close an IF or SWITCH and join type information from all paths.
        Sources: [PROJ] IF-THEN / SWITCH-CASE (OIC ends both), [GRAM] if_then / switch_case,
        [RUSTC] join at a merge point, [CI-11] 11.3.6 (static analysis considers both branches)."""
        cur.next(); cur.expect_end()
        top = self.frames[-1]
        if top.kind == "IF":
            if "ya" not in top.seen:
                self.err(line, "O RLY? block has no YA RLY")
            top.branch_ends.append(self._snapshot())
            if "nowai" not in top.seen:
                top.branch_ends.append(top.snapshot)   # the implicit empty else
            self._merge(top.branch_ends)
        elif top.kind == "SWITCH":
            if "case" not in top.seen:
                self.err(line, "WTF? block has no OMG case")
            self._weaken_to(top.snapshot)
        else:
            self.err(line, "OIC without a matching O RLY? or WTF?" if top.kind == "TOP"
                     else f"OIC found, but {self._open_name(top)} is still open")
            return
        self.frames.pop()

    # ---- loops --------------------------------------------------------------
    def _loop_start(self, cur: Cursor, line: int, idx: int) -> None:
        """`IM IN YR label UPPIN|NERFIN YR var [TIL|WILE expr]`.
        Sources: [PROJ] LOOPS (label; UPPIN/NERFIN; the variable must be declared and
        numeric-castable; TIL/WILE), [TUT-LOL] Loops, [GRAM] loop / loop_op / loop_cond,
        [LEX] (Loop Identifier), [CI-11] 11.3.6 (a loop body is visited once)."""
        cur.next()
        label = cur.expect_class(CLASS_LOOP_IDENT, "a loop label after IM IN YR").lexeme
        op = cur.next()
        if kw(op) not in ("UPPIN", "NERFIN"):
            raise SyntaxProblem(f"expected UPPIN or NERFIN but found {op.lexeme!r}")
        cur.expect_kw("YR", f" after {op.lexeme}")
        var = cur.expect_class(CLASS_VAR_IDENT, "a loop variable")
        if any(f.kind == "LOOP" and f.label == label for f in self.frames):
            self.err(line, f"loop label '{label}' is already used by an enclosing loop")
        sym = self._lookup(var.lexeme, line)
        if sym is not None:
            if sym.type == NOOB:
                self.err(line, f"loop variable '{var.lexeme}' is NOOB and cannot be cast to a number for {op.lexeme}")
            elif sym.type == YARN:
                self.warn(line, f"loop variable '{var.lexeme}' is a YARN; it must hold a numeric string for {op.lexeme}")
            elif var.lexeme != "IT" and sym.type not in (NUMBR, NUMBAR):
                sym.type = ANY
            self._assigned_in_loop(idx)
        if not cur.at_end():
            c = cur.next()
            if kw(c) not in ("TIL", "WILE"):
                raise SyntaxProblem(f"expected TIL or WILE but found {c.lexeme!r}")
            self.it_type = ANY
            self._expr(cur, line)
            cur.expect_end()
        self.it_type = ANY
        self._push("LOOP", line, label)

    def _assigned_in_loop(self, idx: int) -> None:
        """Pre-scan the loop body: any variable assigned, read-in or re-cast inside it gets type ANY
        on entry, because on the second iteration it may have the type set at the bottom of the
        body. Sources: [RUSTC] (a back-edge feeds the end-of-body state into the loop head, which
        is why dataflow joins there), [CI-11] 11.3.6 (analysis visits the body only once, so this
        conservative shortcut stands in for iterating to a fixed point). Simplification: [OWN]."""
        depth = 0
        for _, toks in self.lines[idx + 1:]:
            k = kw(toks[0])
            if k == "IM IN YR":
                depth += 1
            elif k == "IM OUTTA YR":
                if depth == 0:
                    break
                depth -= 1
            target = None
            if toks[0].classification == CLASS_VAR_IDENT and len(toks) > 1 and kw(toks[1]) in ("R", "IS NOW A"):
                target = toks[0].lexeme
            elif k == "GIMMEH" and len(toks) > 1:
                target = toks[1].lexeme
            if target in self.scope:
                self.scope[target].type = ANY
                self.scope[target].value = None

    def _loop_end(self, cur: Cursor, line: int) -> None:
        """`IM OUTTA YR label` must match the innermost open loop.
        Sources: [PROJ] LOOPS ('the <label> ... is used as a delimiter, especially ... nested
        loops'), [GRAM] loop; [TUT-LOL] Loops says the label is only a marker, [PROJ] is stricter.
        Join at loop exit (body may run zero times): [RUSTC]."""
        cur.next()
        label = cur.expect_class(CLASS_LOOP_IDENT, "a loop label after IM OUTTA YR").lexeme
        cur.expect_end()
        if not any(f.kind == "LOOP" for f in self._frames_in_scope()):
            self.err(line, f"IM OUTTA YR {label} has no matching IM IN YR")
            return
        while self.frames[-1].kind != "LOOP":
            f = self.frames.pop()
            self.err(f.line, f"{self._open_name(f)} opened here is not closed before the loop ends")
        f = self.frames.pop()
        if f.label != label:
            self.err(line, f"IM OUTTA YR {label} does not match the innermost loop '{f.label}' (line {f.line})")
        self._weaken_to(f.snapshot)

    def _frames_in_scope(self) -> List[Frame]:
        """Frames belonging to the function (or main program) currently being analysed.
        Source: [CI-11] 11.5.1 (track the enclosing function so a nested function body is judged on
        its own), [OWN]."""
        for i in range(len(self.frames) - 1, -1, -1):
            if self.frames[i].kind == "FUNC":
                return self.frames[i + 1:]
        return self.frames[1:]

    # ---- functions ----------------------------------------------------------
    def _func_start(self, cur: Cursor, line: int) -> None:
        """Enter a function: a fresh scope that holds only the parameters.
        Sources: [PROJ] FUNCTIONS ('Functions cannot access identifiers outside of it', pass by
        value, parameters become variables), [TUT-LOL] Functions ('functions do not
        have access to the outer/calling code block's variables') and Variables - Scope,
        [GRAM] function_def, [CI-11] 11.3.5 (a function introduces a scope and binds its
        parameters in it; its body is analysed immediately), [CORNELL] (new scope on entry)."""
        cur.next()
        name = cur.expect_class(CLASS_FUNC_IDENT, "a function name").lexeme
        params = self._params(cur)
        if self.in_function or len(self.frames) > 1:
            self.err(line, "functions cannot be defined inside another function or a block")
        if self.phase == "DECL":
            self.err(line, "functions cannot be defined inside WAZZUP")
        f = self._push("FUNC", line, name)
        self.in_function = True
        self._saved_it_set = self.it_set   # [TUT-LOL] Expression Statements: IT is local to its scope
        self.it_set = False
        fn_it = Symbol("IT", NOOB, 0, True, value=None)
        fn_it.used = True
        self.scope = {"IT": fn_it}
        for p in params:
            if p == "IT":
                self.err(line, f"IT is the implicit variable and cannot be a parameter in function '{name}'")
            elif p in self.scope:
                self.err(line, f"duplicate parameter '{p}' in function '{name}'")
            else:
                self.scope[p] = Symbol(p, ANY, line, True, is_param=True)
        f.snapshot = {}

    def _func_end(self, cur: Cursor, line: int) -> None:
        """Leave the function, restore the global scope, warn about unused locals.
        Sources: [PROJ] FUNCTIONS - Definition (IF U SAY SO), [GRAM] function_def, [CI-11]
        11.3.5 (end the function scope) and Challenge 3 (report a local that is never used),
        [CORNELL] (pop on exit)."""
        cur.next(); cur.expect_end()
        if not self.in_function:
            self.err(line, "IF U SAY SO without a matching HOW IZ I")
            return
        while self.frames[-1].kind != "FUNC":
            f = self.frames.pop()
            self.err(f.line, f"{self._open_name(f)} opened here is not closed before the function ends")
        self.frames.pop()
        for s in self.scope.values():
            if s.name != "IT" and not s.used and not s.is_param:
                self.warn(s.line, f"local variable '{s.name}' is declared but never used")
        self.scope, self.in_function = self.globals, False
        self.it_set = self._saved_it_set

    # ---- end of file --------------------------------------------------------
    @staticmethod
    def _open_name(f: Frame) -> str:
        """Human-readable name for an open block (message text only). Source: [OWN]."""
        return {"IF": "O RLY?", "SWITCH": "WTF?", "LOOP": f"loop '{f.label}'",
                "FUNC": f"function '{f.label}'"}.get(f.kind, f.kind)

    def _finish(self) -> None:
        """End-of-file checks: HAI/KTHXBYE present, nothing left open, unused globals.
        Sources: [PROJ] FILE NAMING, [GRAM] program, [CI-11] 11.5 (warn on a variable that is never
        used)."""
        if not self.lines:
            self.err(1, "empty program: expected HAI ... KTHXBYE")
            return
        if not self.seen_hai:
            self.err(self.first_line, "missing HAI")
        if not self.seen_kthxbye:
            self.err(self.last_line, "missing KTHXBYE")
        if self.phase == "DECL" and not self.seen_kthxbye:
            self.err(self.last_line, "WAZZUP block was never closed with BUHBYE")
        for f in self.frames[1:]:
            self.err(f.line, f"{self._open_name(f)} opened here is never closed")
        for s in self.globals.values():
            if s.name != "IT" and not s.used:
                self.warn(s.line, f"variable '{s.name}' is declared but never used")

    # ------------------------------------------------------------ runtime execution
    # References for runtime execution & tree-walk interpreter implementation:
    #   [CI-7] Evaluating Expressions: https://craftinginterpreters.com/evaluating-expressions.html
    #   [CI-8] Statements and State: https://craftinginterpreters.com/statements-and-state.html
    #   [CI-9] Control Flow: https://craftinginterpreters.com/control-flow.html
    #   [CI-10] Functions: https://craftinginterpreters.com/functions.html
    #   [TUT-LOL] LOLCODE Syntax Guide: https://www.tutorialspoint.com/lolcode/lolcode_syntax.htm
    @staticmethod
    def _set_symbol(sym: Symbol, v: Val, initialized: Optional[bool] = None) -> None:
        sym.type = v.type
        sym.value = None if v.type == NOOB else v.const
        sym.initialized = (v.type != NOOB) if initialized is None else initialized

    @staticmethod
    def _to_troof(v: Val) -> bool:
        """Implicit cast to TROOF: NOOB, 0, 0.0, '' and FAIL are False; everything else is True."""
        if v.type == NOOB or v.const is None:
            return False
        if v.type == TROOF:
            return bool(v.const)
        if v.type in (NUMBR, NUMBAR):
            return v.const != 0
        if v.type == YARN:
            return v.const != ""
        return bool(v.const)

    @staticmethod
    def _rt_to_num(v: Val, op: str, line: int) -> Val:
        """Implicit numeric cast for arithmetic and loop UPPIN/NERFIN."""
        if v.type == NUMBR:
            return Val(NUMBR, int(v.const))
        if v.type == NUMBAR:
            return Val(NUMBAR, float(v.const))
        if v.type == TROOF:
            return Val(NUMBR, 1 if v.const else 0)
        if v.type == NOOB:
            raise RuntimeProblem(line, f"{op}: a NOOB (untyped/uninitialized) value cannot be implicitly cast to a number")
        if v.type == YARN:
            s = v.const if isinstance(v.const, str) else ""
            if not re.fullmatch(r"-?[0-9]+(\.[0-9]+)?", s):
                raise RuntimeProblem(line, f'{op}: YARN "{s}" cannot be cast to a number')
            return Val(NUMBAR, float(s)) if "." in s else Val(NUMBR, int(s))
        raise RuntimeProblem(line, f"{op}: cannot cast {v.type} to a number")

    @staticmethod
    def _rt_to_yarn(v: Val, line: int) -> str:
        """Implicit YARN cast for SMOOSH."""
        if v.type == YARN:
            return str(v.const)
        if v.type in (NUMBR, NUMBAR):
            return str(v.const)
        if v.type == TROOF:
            return "WIN" if v.const else "FAIL"
        raise RuntimeProblem(line, "SMOOSH: a NOOB (untyped/uninitialized) value cannot be implicitly cast to YARN")

    @staticmethod
    def _to_visible_str(v: Val) -> str:
        """String conversion for VISIBLE (allows printing NOOB without error)."""
        if v.type == NOOB or v.const is None:
            return "NOOB"
        if v.type == TROOF:
            return "WIN" if v.const else "FAIL"
        return str(v.const)

    def _rt_cast(self, v: Val, target: str, line: int) -> Val:
        """Explicit cast via MAEK / IS NOW A."""
        if target == NOOB:
            return Val(NOOB, None)
        if target == TROOF:
            return Val(TROOF, self._to_troof(v))
        if target == YARN:
            if v.type == NOOB or v.const is None:
                return Val(YARN, "")
            if v.type == TROOF:
                return Val(YARN, "WIN" if v.const else "FAIL")
            return Val(YARN, str(v.const))
        if target == NUMBR:
            if v.type == NOOB:
                return Val(NUMBR, 0)
            if v.type == NUMBR:
                return Val(NUMBR, int(v.const))
            if v.type == NUMBAR:
                return Val(NUMBR, int(v.const))
            if v.type == TROOF:
                return Val(NUMBR, 1 if v.const else 0)
            if v.type == YARN:
                s = v.const if isinstance(v.const, str) else ""
                if not re.fullmatch(r"-?[0-9]+(\.[0-9]+)?", s):
                    raise RuntimeProblem(line, f'cannot cast YARN "{s}" to NUMBR')
                return Val(NUMBR, int(float(s)) if "." in s else int(s))
        if target == NUMBAR:
            if v.type == NOOB:
                return Val(NUMBAR, 0.0)
            if v.type in (NUMBR, NUMBAR):
                return Val(NUMBAR, float(v.const))
            if v.type == TROOF:
                return Val(NUMBAR, 1.0 if v.const else 0.0)
            if v.type == YARN:
                s = v.const if isinstance(v.const, str) else ""
                if not re.fullmatch(r"-?[0-9]+(\.[0-9]+)?", s):
                    raise RuntimeProblem(line, f'cannot cast YARN "{s}" to NUMBAR')
                return Val(NUMBAR, float(s))
        raise RuntimeProblem(line, f"cannot cast {v.type} to {target}")

    @staticmethod
    def _rt_equal(a: Val, b: Val) -> bool:
        """BOTH SAEM equality: numeric promotion between NUMBR/NUMBAR, no other implicit casts."""
        if a.type in (NUMBR, NUMBAR) and b.type in (NUMBR, NUMBAR):
            return a.const == b.const
        if a.type != b.type:
            return False
        if a.type == NOOB:
            return True
        return a.const == b.const

    def _rt_arith(self, op: str, a: Val, b: Val, line: int) -> Val:
        na, nb = self._rt_to_num(a, op, line), self._rt_to_num(b, op, line)
        is_float = NUMBAR in (na.type, nb.type)
        va = float(na.const) if is_float else int(na.const)
        vb = float(nb.const) if is_float else int(nb.const)
        res_type = NUMBAR if is_float else NUMBR
        if op == "SUM OF":
            res = va + vb
        elif op == "DIFF OF":
            res = va - vb
        elif op == "PRODUKT OF":
            res = va * vb
        elif op == "QUOSHUNT OF":
            if vb == 0:
                raise RuntimeProblem(line, "QUOSHUNT OF: division by zero")
            res = (va / vb) if is_float else int(va / vb)
        elif op == "MOD OF":
            if vb == 0:
                raise RuntimeProblem(line, "MOD OF: division by zero")
            res = math.fmod(va, vb) if is_float else (va - int(va / vb) * vb)
        elif op == "BIGGR OF":
            res = va if va >= vb else vb
        elif op == "SMALLR OF":
            res = va if va <= vb else vb
        else:
            raise RuntimeProblem(line, f"unknown arithmetic operator {op!r}")
        return Val(res_type, float(res) if is_float else int(res))

    def _rt_lookup(self, name: str, line: int) -> Symbol:
        sym = self.scope.get(name)
        if sym is None:
            raise RuntimeProblem(line, f"variable '{name}' was not declared on this execution path")
        return sym

    def _eval_expr(self, cur: Cursor, line: int) -> Val:
        """Evaluate prefix-notation expression at runtime.
        Sources: [CI-7] 7.2 (evaluating expressions recursively), [TUT-LOL] Operators."""
        t = cur.peek()
        if t is None:
            raise RuntimeProblem(line, "unexpected end of expression")
        k = kw(t)
        if t.classification == CLASS_STRING_DELIMITER:
            return self._yarn(cur)
        if t.classification == CLASS_LITERAL:
            cur.next()
            return self._literal_val(t)
        if t.classification == CLASS_VAR_IDENT:
            cur.next()
            sym = self._rt_lookup(t.lexeme, line)
            return Val(sym.type, sym.value)
        if k in ARITH:
            cur.next()
            a = self._eval_expr(cur, line)
            cur.match("AN")
            b = self._eval_expr(cur, line)
            return self._rt_arith(k, a, b, line)
        if k in BOOL2:
            cur.next()
            a = self._eval_expr(cur, line)
            cur.match("AN")
            b = self._eval_expr(cur, line)
            ba, bb = self._to_troof(a), self._to_troof(b)
            if k == "BOTH OF":
                return Val(TROOF, ba and bb)
            if k == "EITHER OF":
                return Val(TROOF, ba or bb)
            return Val(TROOF, ba != bb)
        if k == "NOT":
            cur.next()
            return Val(TROOF, not self._to_troof(self._eval_expr(cur, line)))
        if k in COMPARE:
            cur.next()
            a = self._eval_expr(cur, line)
            cur.match("AN")
            b = self._eval_expr(cur, line)
            eq = self._rt_equal(a, b)
            return Val(TROOF, eq if k == "BOTH SAEM" else not eq)
        if k in INFINITE:
            cur.next()
            vals = [self._eval_expr(cur, line)]
            while cur.match("AN"):
                vals.append(self._eval_expr(cur, line))
            cur.match("MKAY")
            res = all(self._to_troof(v) for v in vals) if k == "ALL OF" else any(self._to_troof(v) for v in vals)
            return Val(TROOF, res)
        if k == "SMOOSH":
            cur.next()
            vals = [self._eval_expr(cur, line)]
            while cur.match("AN"):
                vals.append(self._eval_expr(cur, line))
            return Val(YARN, "".join(self._rt_to_yarn(v, line) for v in vals))
        if k == "MAEK":
            cur.next()
            v = self._eval_expr(cur, line)
            cur.match("A")
            tt = cur.next().lexeme
            return self._rt_cast(v, tt, line)
        if k == "I IZ":
            return self._rt_call(cur, line)
        raise RuntimeProblem(line, f"unexpected token {t.lexeme!r} in expression")

    def _rt_call(self, cur: Cursor, line: int) -> Val:
        """Call a function at runtime: push new scope, bind parameters, run body, catch return.
        Sources: [CI-10] 10.4 (function calls, fresh environment for parameters, return unwinding),
        [TUT-LOL] Functions."""
        cur.next()  # I IZ
        name = cur.next().lexeme
        args: List[Val] = []
        if cur.match("YR"):
            args.append(self._eval_expr(cur, line))
            while cur.match("AN YR"):
                args.append(self._eval_expr(cur, line))
        cur.match("MKAY")

        if self._call_depth >= MAX_CALL_DEPTH:
            raise RuntimeProblem(line, f"maximum recursion depth ({MAX_CALL_DEPTH}) exceeded calling '{name}'")

        fn = self.functions[name]
        fn_start, fn_end = self._func_ranges[name]
        fn_it = Symbol("IT", NOOB, 0, True, value=None)
        fn_it.used = True
        local_scope: Dict[str, Symbol] = {"IT": fn_it}
        for p_name, arg_val in zip(fn.params, args):
            local_scope[p_name] = Symbol(
                p_name, arg_val.type, fn.line, arg_val.type != NOOB,
                is_param=True, value=arg_val.const,
            )

        prev_scope = self.scope
        self.scope = local_scope
        self._call_depth += 1
        try:
            self._exec_range(fn_start + 1, fn_end)
        except _ReturnSignal as ret:
            return ret.val
        except _BreakSignal:
            return Val(NOOB, None)
        finally:
            self._call_depth -= 1
            self.scope = prev_scope
        return Val(local_scope["IT"].type, local_scope["IT"].value)

    def _exec_if(self, pc: int) -> int:
        """Execute O RLY? / YA RLY / MEBBE / NO WAI / OIC conditional block.
        Sources: [CI-9] 9.2 (conditional execution branches), [TUT-LOL] Decision Making."""
        clauses: List[Tuple[int, str]] = []
        oic_idx = pc + 1
        depth = 0
        i = pc + 1
        while i < len(self.lines):
            k = kw(self.lines[i][1][0])
            if k in ("O RLY?", "WTF?"):
                depth += 1
            elif k == "OIC":
                if depth == 0:
                    oic_idx = i
                    break
                depth -= 1
            elif depth == 0 and k in ("YA RLY", "MEBBE", "NO WAI"):
                clauses.append((i, k))
            i += 1

        def body_end(c_pos: int) -> int:
            return clauses[c_pos + 1][0] if c_pos + 1 < len(clauses) else oic_idx

        it_sym = self.scope["IT"]
        if self._to_troof(Val(it_sym.type, it_sym.value)):
            if clauses and clauses[0][1] == "YA RLY":
                self._exec_range(clauses[0][0] + 1, body_end(0))
            return oic_idx + 1

        for pos, (c_idx, c_kw) in enumerate(clauses):
            if c_kw == "YA RLY":
                continue
            if c_kw == "MEBBE":
                c_line, c_toks = self.lines[c_idx]
                c_cur = Cursor(c_toks)
                c_cur.next()
                v = self._eval_expr(c_cur, c_line)
                self._set_symbol(self.scope["IT"], v)
                if self._to_troof(v):
                    self._exec_range(c_idx + 1, body_end(pos))
                    return oic_idx + 1
            elif c_kw == "NO WAI":
                self._exec_range(c_idx + 1, body_end(pos))
                return oic_idx + 1
        return oic_idx + 1

    def _exec_wtf(self, pc: int) -> int:
        """Execute WTF? / OMG / OMGWTF / OIC switch-case with fall-through and GTFO.
        Sources: [CI-9] 9.5 (branching and break signals), [TUT-LOL] Decision Making."""
        cases: List[Tuple[int, Val]] = []
        default_idx: Optional[int] = None
        oic_idx = pc + 1
        depth = 0
        i = pc + 1
        while i < len(self.lines):
            _, c_toks = self.lines[i]
            k = kw(c_toks[0])
            if k in ("O RLY?", "WTF?"):
                depth += 1
            elif k == "OIC":
                if depth == 0:
                    oic_idx = i
                    break
                depth -= 1
            elif depth == 0 and k == "OMG":
                c_cur = Cursor(c_toks)
                c_cur.next()
                cases.append((i, self._case_literal(c_cur)))
            elif depth == 0 and k == "OMGWTF":
                default_idx = i
            i += 1

        it_sym = self.scope["IT"]
        it_val = Val(it_sym.type, it_sym.value)
        start_idx: Optional[int] = None
        for c_idx, lit_val in cases:
            if self._rt_equal(it_val, lit_val):
                start_idx = c_idx
                break
        if start_idx is None:
            start_idx = default_idx

        if start_idx is not None:
            try:
                self._exec_range(start_idx + 1, oic_idx)
            except _BreakSignal:
                pass
        return oic_idx + 1

    def _exec_loop(self, pc: int) -> int:
        """Execute IM IN YR / UPPIN/NERFIN / TIL/WILE loop.
        Sources: [CI-9] 9.3 (loops and condition re-evaluation), [TUT-LOL] Loops."""
        line, toks = self.lines[pc]
        cur = Cursor(toks)
        cur.next()  # IM IN YR
        label = cur.next().lexeme
        op_kw = kw(cur.next()) or "UPPIN"
        cur.next()  # YR
        var_name = cur.next().lexeme
        cond_kind: Optional[str] = None
        cond_start = cur.i
        if not cur.at_end():
            cond_kind = kw(cur.next())
            cond_start = cur.i
        cond_toks = toks[cond_start:]

        end_idx = pc + 1
        depth = 0
        i = pc + 1
        while i < len(self.lines):
            k = kw(self.lines[i][1][0])
            if k == "IM IN YR":
                depth += 1
            elif k == "IM OUTTA YR":
                if depth == 0:
                    end_idx = i
                    break
                depth -= 1
            i += 1

        iterations = 0
        while True:
            iterations += 1
            if iterations > MAX_LOOP_ITERATIONS:
                raise RuntimeProblem(line, f"loop '{label}' exceeded {MAX_LOOP_ITERATIONS} iterations")
            if cond_kind is not None:
                cond_val = self._eval_expr(Cursor(cond_toks), line)
                cond_bool = self._to_troof(cond_val)
                if (cond_kind == "TIL" and cond_bool) or (cond_kind == "WILE" and not cond_bool):
                    break
            try:
                self._exec_range(pc + 1, end_idx)
            except _BreakSignal:
                break
            sym = self._rt_lookup(var_name, line)
            num = self._rt_to_num(Val(sym.type, sym.value), op_kw, line)
            delta = 1 if op_kw == "UPPIN" else -1
            res = (float(num.const) + delta) if num.type == NUMBAR else (int(num.const) + delta)
            self._set_symbol(sym, Val(num.type, res))
        return end_idx + 1

    def _exec_one(self, pc: int) -> int:
        line, toks = self.lines[pc]
        cur = Cursor(toks)
        k = kw(toks[0])

        if k in ("HAI", "WAZZUP", "BUHBYE", "KTHXBYE", "OMG", "OMGWTF"):
            return pc + 1
        if k == "HOW IZ I":
            name = toks[1].lexeme
            if name in self._func_ranges:
                return self._func_ranges[name][1] + 1
            i = pc + 1
            while i < len(self.lines) and kw(self.lines[i][1][0]) != "IF U SAY SO":
                i += 1
            return i + 1
        if k == "I HAS A":
            cur.next()
            name = cur.next().lexeme
            has_init = cur.match("ITZ")
            v = self._eval_expr(cur, line) if has_init else Val(NOOB, None)
            if name in self.scope:
                self._set_symbol(self.scope[name], v, initialized=has_init and v.type != NOOB)
            else:
                self.scope[name] = Symbol(name, v.type, line, has_init and v.type != NOOB, value=v.const)
            return pc + 1
        if k == "VISIBLE":
            cur.next()
            parts = [self._to_visible_str(self._eval_expr(cur, line))]
            while not cur.at_end():
                cur.match("AN")
                parts.append(self._to_visible_str(self._eval_expr(cur, line)))
            self.output_fn("".join(parts))
            return pc + 1
        if k == "GIMMEH":
            cur.next()
            name = cur.next().lexeme
            try:
                raw = self.input_fn()
            except EOFError:
                raw = ""
            if raw.endswith("\r\n"):
                raw = raw[:-2]
            elif raw.endswith("\n"):
                raw = raw[:-1]
            self._set_symbol(self._rt_lookup(name, line), Val(YARN, raw), initialized=True)
            return pc + 1
        if k == "O RLY?":
            return self._exec_if(pc)
        if k == "WTF?":
            return self._exec_wtf(pc)
        if k == "GTFO":
            raise _BreakSignal()
        if k == "IM IN YR":
            return self._exec_loop(pc)
        if k == "FOUND YR":
            cur.next()
            raise _ReturnSignal(self._eval_expr(cur, line))

        first = toks[0]
        if first.classification == CLASS_VAR_IDENT and kw(cur.peek(1)) == "R":
            name = cur.next().lexeme
            cur.next()
            v = self._eval_expr(cur, line)
            self._set_symbol(self._rt_lookup(name, line), v)
            return pc + 1
        if first.classification == CLASS_VAR_IDENT and kw(cur.peek(1)) == "IS NOW A":
            name = cur.next().lexeme
            cur.next()
            target = cur.next().lexeme
            sym = self._rt_lookup(name, line)
            v = self._rt_cast(Val(sym.type, sym.value), target, line)
            self._set_symbol(sym, v)
            return pc + 1

        v = self._eval_expr(cur, line)
        self._set_symbol(self.scope["IT"], v)
        return pc + 1

    def _exec_range(self, start: int, end: int, stop_at_kthxbye: bool = False) -> None:
        pc = start
        while pc < end:
            k = kw(self.lines[pc][1][0])
            if stop_at_kthxbye and k == "KTHXBYE":
                break
            pc = self._exec_one(pc)

    def _index_function_bodies(self) -> None:
        self._func_ranges.clear()
        i = 0
        while i < len(self.lines):
            _, toks = self.lines[i]
            if kw(toks[0]) == "HOW IZ I" and len(toks) > 1:
                name = toks[1].lexeme
                j = i + 1
                while j < len(self.lines) and kw(self.lines[j][1][0]) != "IF U SAY SO":
                    j += 1
                if j < len(self.lines):
                    self._func_ranges[name] = (i, j)
                i = j + 1
            else:
                i += 1

    def _execute(self) -> None:
        """Pass 3: execute the validated LOLCODE program and populate Symbol.value entries.
        Sources: [CI-8] 8.1-8.5 (tree-walk statement evaluation and environment state),
        [CI-10] (call stack), [TUT-LOL] Program Structure."""
        self._index_function_bodies()
        for name, sym in self.globals.items():
            sym.type = NOOB
            sym.value = None
            sym.initialized = (name == "IT")
        self.scope = self.globals
        self._call_depth = 0
        try:
            self._exec_range(0, len(self.lines), stop_at_kthxbye=True)
        except RuntimeProblem as e:
            self.err(e.line, e.message, "Runtime")


# --------------------------------------------------------------------------- public API
def analyze_source(source: str,
                   input_fn: Callable[[], str] = input,
                   output_fn: Callable[[str], None] = print,
                   execute: bool = True) -> Tuple[List[Issue], SemanticAnalyzer]:
    """Lex, then analyze (and execute when valid). Lexical errors stop semantic analysis.
    Sources: [CI-11] 11.4.3 (don't run the resolver if earlier phases reported errors),
    [CORNELL] (lexical -> syntactic -> semantic phase ordering), [LEX] tokenize_source / LexError."""
    tokens, lex_errors = tokenize_source(source)
    sa = SemanticAnalyzer(tokens, input_fn=input_fn, output_fn=output_fn)
    if lex_errors:
        sa.issues = [Issue(e.line, "error", "Lexical", f"{e.message}: {e.lexeme!r}") for e in lex_errors]
        return sa.issues, sa
    return sa.analyze(execute=execute), sa


def _format_symbol_value(s: Symbol) -> str:
    """Format a Symbol's stored value for single-line CLI symbol-table display."""
    if s.type == NOOB or (s.value is None and s.type != ANY):
        return "NOOB"
    if s.value is None and s.type == ANY:
        return "?"
    if s.type == TROOF:
        return "WIN" if s.value else "FAIL"
    if s.type == YARN:
        escaped = (
            str(s.value)
            .replace("\n", "\\n")
            .replace("\r", "\\r")
            .replace("\t", "\\t")
            .replace("\a", "\\a")
        )
        return f'"{escaped}"'
    return str(s.value)


def print_report(issues: List[Issue], sa: SemanticAnalyzer) -> None:
    """CLI report with a symbol table. Source: [LEX] print_lexeme_table (same presentation style)."""
    errors = [i for i in issues if i.severity == "error"]
    for i in issues:
        print(i)
    has_lex_err = any(i.category == "Lexical" for i in issues)
    if not has_lex_err and sa.lines and (sa.globals or sa.functions):
        print(f"\n{'Symbol':<16}{'Kind':<10}{'Line':<6}{'Type / Params':<20}Value")
        print("-" * 72)
        for s in sa.globals.values():
            line_col = "-" if s.name == "IT" else str(s.line)
            print(f"{s.name:<16}{'variable':<10}{line_col:<6}{s.type:<20}{_format_symbol_value(s)}")
        for f in sa.functions.values():
            params_col = f"({', '.join(f.params)})"
            print(f"{f.name:<16}{'function':<10}{f.line:<6}{params_col:<20}-")
    print(f"\n{len(errors)} error(s), {len(issues) - len(errors)} warning(s)")


# --------------------------------------------------------------------------- self-test
def _self_test() -> None:
    """Assertions over valid and invalid programs. Sources: programs adapted from the examples in
    [PROJ] (loops, arithmetic, boolean nesting, comments) and [TUT-LOL] (`BOTH SAEM "3" AN 3`
    is FAIL; switch literals must be unique); the remaining cases are [OWN]."""
    def run(src, stdin_lines=None):
        inputs = iter(stdin_lines if stdin_lines is not None else ["Alice"])
        outputs: List[str] = []
        issues, _ = analyze_source(src, input_fn=lambda: next(inputs, ""), output_fn=outputs.append)
        return [i for i in issues if i.severity == "error"], [i for i in issues if i.severity == "warning"]

    def has(msgs, text):
        return any(text in e.message for e in msgs)

    good = (
        "HAI\nWAZZUP\n  I HAS A temp ITZ 2\n  I HAS A name\n  I HAS A r ITZ 0\nBUHBYE\n"
        "GIMMEH name\nVISIBLE \"Hi \" name\n"
        "IM IN YR print10 UPPIN YR temp TIL BOTH SAEM temp AN 10\n  VISIBLE temp\nIM OUTTA YR print10\n"
        "r R I IZ add YR 1 AN YR 2 MKAY\nVISIBLE r\n"
        "BOTH SAEM r AN 3\nO RLY?\nYA RLY\n  VISIBLE \"yes\"\nNO WAI\n  VISIBLE \"no\"\nOIC\n"
        "r\nWTF?\nOMG 3\n  VISIBLE \"three\"\n  GTFO\nOMGWTF\n  VISIBLE \"other\"\nOIC\n"
        "KTHXBYE\n"
        "HOW IZ I add YR a AN YR b\n  FOUND YR SUM OF a AN b\nIF U SAY SO\n"
    )
    e, w = run(good)
    assert e == [], e

    assert has(run("HAI\nVISIBLE x\nKTHXBYE\n")[0], "used before being declared")
    assert has(run("HAI\nWAZZUP\nI HAS A x\nI HAS A x\nBUHBYE\nKTHXBYE\n")[0], "already declared")
    assert has(run("HAI\nWAZZUP\nI HAS A x ITZ x\nBUHBYE\nKTHXBYE\n")[0], "own initializer")      # [CI-11] 11.3.2
    assert has(run("HAI\nI HAS A x\nKTHXBYE\n")[0], "inside the WAZZUP")
    assert has(run("HAI\nVISIBLE 1\n")[0], "missing KTHXBYE")
    assert has(run("VISIBLE 1\nKTHXBYE\n")[0], "start with HAI")
    assert has(run("HAI\nWAZZUP\nI HAS A s ITZ \"abc\"\nBUHBYE\nVISIBLE SUM OF 1 AN \"abc\"\nKTHXBYE\n")[0], "cannot be cast")
    assert has(run("HAI\nWAZZUP\nI HAS A n\nBUHBYE\nVISIBLE SUM OF n AN 1\nKTHXBYE\n")[0], "NOOB")
    assert not run("HAI\nVISIBLE SUM OF \"2\" AN \"7\"\nKTHXBYE\n")[0]
    assert has(run("HAI\nVISIBLE QUOSHUNT OF 5 AN 0\nKTHXBYE\n")[0], "division by constant zero")
    assert has(run("HAI\nVISIBLE ALL OF WIN AN ANY OF WIN AN FAIL MKAY MKAY\nKTHXBYE\n")[0], "cannot be nested")
    assert has(run("HAI\nVISIBLE ALL OF WIN AN FAIL\nKTHXBYE\n")[0], "MKAY")
    assert not run("HAI\nVISIBLE ALL OF NOT WIN AN BOTH OF WIN AN FAIL AN EITHER OF WIN AN FAIL MKAY\nKTHXBYE\n")[0]
    assert has(run("HAI\nVISIBLE SUM OF 1 2\nKTHXBYE\n")[0], "'AN'")
    assert has(run("HAI\nVISIBLE SUM OF 1 AN SMOOSH \"a\" AN \"b\"\nKTHXBYE\n")[0], "SMOOSH cannot be nested")
    assert has(run("HAI\nGTFO\nKTHXBYE\n")[0], "GTFO is only valid")
    assert has(run("HAI\nFOUND YR 1\nKTHXBYE\n")[0], "only valid inside a function")
    # functions
    assert has(run("HAI\nVISIBLE I IZ f MKAY\nKTHXBYE\n")[0], "undefined function")
    assert has(run("HAI\nVISIBLE I IZ f YR 1 MKAY\nKTHXBYE\nHOW IZ I f\nFOUND YR 1\nIF U SAY SO\n")[0], "takes 0")
    assert has(run("HAI\nWAZZUP\nI HAS A g ITZ 1\nBUHBYE\nKTHXBYE\nHOW IZ I f\nFOUND YR g\nIF U SAY SO\n")[0], "outer variable")
    assert has(run("HOW IZ I f\nIF U SAY SO\nHOW IZ I f\nIF U SAY SO\nHAI\nKTHXBYE\n")[0], "already defined")
    assert not run("HOW IZ I f\nVISIBLE 1\nIF U SAY SO\nHAI\nVISIBLE I IZ f MKAY\nKTHXBYE\n")[0]
    # loops / switch / if
    assert has(run("HAI\nWAZZUP\nI HAS A i ITZ 0\nBUHBYE\nIM IN YR a UPPIN YR i TIL BOTH SAEM i AN 3\nIM OUTTA YR b\nKTHXBYE\n")[0], "does not match")
    assert has(run("HAI\nIM IN YR a UPPIN YR zz TIL WIN\nIM OUTTA YR a\nKTHXBYE\n")[0], "used before being declared")
    assert has(run("HAI\nWAZZUP\nI HAS A n\nBUHBYE\nIM IN YR a UPPIN YR n TIL WIN\nIM OUTTA YR a\nKTHXBYE\n")[0], "NOOB")
    assert has(run("HAI\nWIN\nO RLY?\nVISIBLE 1\nOIC\nKTHXBYE\n")[0], "before any statement")
    assert has(run("HAI\nWIN\nWTF?\nOMG 1\nOMG 1\nOIC\nKTHXBYE\n")[0], "duplicate case")
    assert has(run("HAI\nWIN\nWTF?\nOMG 1\nOMGWTF\nOMG 2\nOIC\nKTHXBYE\n")[0], "default case must be last")
    assert has(run("HAI\nWAZZUP\nI HAS A x ITZ 1\nBUHBYE\nx\nWTF?\nOMG x\nOIC\nKTHXBYE\n")[0], "literal")
    assert has(run("HAI\nWIN\nO RLY?\nYA RLY\nVISIBLE 1\nKTHXBYE\n")[0], "never closed")
    # branch merge makes the type ANY, so no false NOOB error afterwards  [RUSTC] join
    flow = ("HAI\nWAZZUP\nI HAS A n\nI HAS A c ITZ WIN\nBUHBYE\nc\nO RLY?\nYA RLY\nn R 5\nNO WAI\nn R 6\nOIC\n"
            "VISIBLE SUM OF n AN 1\nKTHXBYE\n")
    assert not run(flow)[0]
    # comparison warnings: YARN vs NUMBR warns; NUMBR vs NUMBAR does NOT  [TUT-LOL] Comparison Operators
    e, w = run("HAI\nWAZZUP\nI HAS A u\nBUHBYE\nVISIBLE BOTH SAEM 1 AN \"1\"\nKTHXBYE\n")
    assert e == [] and has(w, "never used") and has(w, "always FAIL")
    e, w = run("HAI\nVISIBLE BOTH SAEM 1 AN 1.0\nKTHXBYE\n")
    assert e == [] and not has(w, "always")
    # lexical errors stop analysis
    assert run("HAI\nVISIBLE 12abc\nKTHXBYE\n")[0][0].category == "Lexical"
    print("lol_semantics self-test: OK")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        toks, lex_errs = tokenize_file(sys.argv[1])
        if lex_errs:
            iss = [Issue(e.line, "error", "Lexical", f"{e.message}: {e.lexeme!r}") for e in lex_errs]
            sa = SemanticAnalyzer([])
        else:
            sa = SemanticAnalyzer(toks)
            iss = sa.analyze()
        print_report(iss, sa)
        sys.exit(1 if any(i.severity == "error" for i in iss) else 0)
    _self_test()
