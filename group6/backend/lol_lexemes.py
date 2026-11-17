#!/usr/bin/env python3
"""
References:
  [CI-4] https://craftinginterpreters.com/scanning.html
  [CORNELL-LEX] https://www.cs.cornell.edu/courses/cs4120/2022sp/notes/lex/
  [WIKI-LEX] https://en.wikipedia.org/wiki/Lexical_analysis
  [WIKIBK-LEX] https://en.wikibooks.org/wiki/Compiler_Construction/Lexical_analysis
  [UC3M-LEX] https://ocw.uc3m.es/pluginfile.php/1845/mod_page/content/12/contents_unit4.pdf
  [PY-RE] https://docs.python.org/3/library/re.html
  [TUT-LOL] https://www.tutorialspoint.com/lolcode/index.htm
  [ESOLANG] https://esolangs.org/wiki/LOLCODE
  [LOL-ORG] https://lolcode.org/
  [OWN] from own module
===================================================================================
"""
import re
import sys
from typing import List, NamedTuple, Optional, Tuple


# represents a single token with its lexeme, classification, line number, and subtype
# Sources: [CI-4] 4.2 (token structure, type, and source position), [WIKI-LEX] (tokens vs lexemes).
class Token(NamedTuple):
    lexeme: str
    classification: str
    line: int = 0
    subtype: str = ""  # extra literal subtype hint (e.g. NUMBR, NUMBAR)

    # returns lexeme and classification tuple for table display
    def as_row(self) -> Tuple[str, str]:
        return (self.lexeme, self.classification)


# stores information about a lexical error
# Sources: [CI-4] 4.1.2 (lexical error reporting), [CORNELL-LEX] (lexical error diagnostics).
class LexError(NamedTuple):
    line: int
    lexeme: str
    message: str

    def __str__(self) -> str:
        return f"Lexical error (line {self.line}): {self.message}: {self.lexeme!r}"


# classification names shared across members
# Sources: [TUT-LOL] (syntax keywords and classification groups), [ESOLANG] (core token vocabulary).
CLASS_STRING_DELIMITER = "String Delimiter"
CLASS_LITERAL = "Literal"
CLASS_TYPE_LITERAL = "Type Literal"
CLASS_VAR_IDENT = "Variable Identifier"
CLASS_FUNC_IDENT = "Function Identifier"
CLASS_LOOP_IDENT = "Loop Identifier"
CLASS_COMMENT = "Comment Keyword"

# keyword table mapping classification to list of keywords
KEYWORD_GROUPS = [
    ("Code Delimiter",               ["HAI", "KTHXBYE"]),
    ("Declaration Block Delimiter",  ["WAZZUP", "BUHBYE"]),
    ("Variable Declaration",         ["I HAS A"]),
    ("Variable Initialization",      ["ITZ"]),
    ("Assignment Keyword",           ["R"]),
    ("Operand Separator",            ["AN"]),
    ("Output Keyword",               ["VISIBLE"]),
    ("Input Keyword",                ["GIMMEH"]),
    ("Concatenation Keyword",        ["SMOOSH"]),
    ("Arithmetic Operator",          ["SUM OF", "DIFF OF", "PRODUKT OF",
                                      "QUOSHUNT OF", "MOD OF",
                                      "BIGGR OF", "SMALLR OF"]),
    ("Comparison Operator",          ["BOTH SAEM", "DIFFRINT"]),
    ("Boolean Operator",             ["BOTH OF", "EITHER OF", "WON OF", "NOT"]),
    ("Infinite Arity Operator",      ["ALL OF", "ANY OF"]),
    ("Operator Delimiter",           ["MKAY"]),
    ("Typecast Keyword",             ["MAEK", "IS NOW A", "A"]),
    ("Conditional Keyword",          ["O RLY?", "YA RLY", "NO WAI", "MEBBE"]),
    ("Switch-Case Keyword",          ["WTF?", "OMG", "OMGWTF"]),
    ("Conditional/Switch Delimiter", ["OIC"]),
    ("Break Keyword",                ["GTFO"]),
    ("Loop Delimiter",               ["IM IN YR", "IM OUTTA YR"]),
    ("Loop Keyword",                 ["UPPIN", "NERFIN", "TIL", "WILE"]),
    ("Function Delimiter",           ["HOW IZ I", "IF U SAY SO"]),
    ("Return Keyword",               ["FOUND YR"]),
    ("Function Call Keyword",        ["I IZ"]),
    ("Parameter Keyword",            ["YR", "AN YR"]),
    (CLASS_COMMENT,                  ["BTW", "OBTW", "TLDR"]),
]

# keywords that indicate the following identifier is a function or loop name
_FUNC_CONTEXT = {"HOW IZ I", "I IZ"}
_LOOP_CONTEXT = {"IM IN YR", "IM OUTTA YR"}

_END = r"(?=\s|$)"  # lexemes must end at whitespace or end of string
_WS = r"[ \t]+"

RE_NUMBAR = r"-?[0-9]+\.[0-9]+"
RE_NUMBR = r"-?[0-9]+"
RE_TROOF = r"WIN|FAIL"
RE_TYPE = r"NOOB|NUMBR|NUMBAR|YARN|TROOF"
RE_IDENT = r"[A-Za-z][A-Za-z0-9_]*"


# builds regex pattern for a keyword joining words with whitespace
# Sources: [PY-RE] (re.escape and regex syntax), [TUT-LOL] (multi-word keywords with arbitrary spacing).
def keyword_regex(lexeme: str) -> str:
    return _WS.join(re.escape(w) for w in lexeme.split()) + _END


# holds compiled regex pattern and its classification info
class PatternEntry(NamedTuple):
    pattern: str
    compiled: "re.Pattern"
    classification: str
    subtype: str
    name: str


# compiles all keyword and literal regex patterns in priority order
# Sources: [CORNELL-LEX] (maximal munch / token precedence), [CI-4] 4.4 (literal and keyword matching priority).
def _build_patterns() -> List[PatternEntry]:
    entries: List[PatternEntry] = []

    # multi-word keywords first, then longer words first
    flat = [(lex, cls) for cls, lexes in KEYWORD_GROUPS for lex in lexes]
    flat.sort(key=lambda p: (-len(p[0].split()), -len(p[0])))
    for lex, cls in flat:
        src = keyword_regex(lex)
        entries.append(PatternEntry(src, re.compile(src), cls, "", lex))

    def lit(name, src, cls, sub):
        full = f"(?:{src})" + _END
        entries.append(PatternEntry(full, re.compile(full), cls, sub, name))

    # literals in priority order before identifiers
    lit("TROOF", RE_TROOF, CLASS_LITERAL, "TROOF")
    lit("TYPE", RE_TYPE, CLASS_TYPE_LITERAL, "TYPE")
    lit("NUMBAR", RE_NUMBAR, CLASS_LITERAL, "NUMBAR")
    lit("NUMBR", RE_NUMBR, CLASS_LITERAL, "NUMBR")
    lit("IDENTIFIER", RE_IDENT, CLASS_VAR_IDENT, "")

    return entries


PATTERNS: List[PatternEntry] = _build_patterns()


# matches the first valid lexeme starting at a given position in text
# Sources: [WIKIBK-LEX] (pattern priority ordering), [PY-RE] (compiled regex matching).
def match_lexeme_at(text: str, pos: int = 0) -> Optional[Tuple[str, str, str, str]]:
    for entry in PATTERNS:
        m = entry.compiled.match(text, pos)
        if m:
            return (m.group(0), entry.classification, entry.subtype, entry.name)
    return None


# classifies a single whole lexeme string into classification and subtype
# Sources: [WIKI-LEX] (lexeme classification against grammar terminals).
def classify_lexeme(lexeme: str) -> Optional[Tuple[str, str]]:
    hit = match_lexeme_at(lexeme, 0)
    if hit and hit[0] == lexeme:
        return (hit[1], hit[2])
    return None


# scans a YARN from opening quote at pos; returns (tokens, errors, new_pos)
# Sources: [CI-4] 4.5.1 (string literal scanning & unclosed string reporting), [TUT-LOL] (string literals and quote escapes).
def _scan_yarn(text: str, pos: int, line_no: int) -> Tuple[List[Token], List[LexError], int]:
    tokens: List[Token] = []
    errors: List[LexError] = []
    n = len(text)

    tokens.append(Token('"', CLASS_STRING_DELIMITER, line_no))
    pos += 1  # consume opening "
    start = pos

    while pos < n:
        # LOLCODE escaped quote :\" stays inside the YARN
        if text[pos] == ":" and pos + 1 < n and text[pos + 1] == '"':
            pos += 2
            continue
        if text[pos] == '"':
            inner = text[start:pos]
            tokens.append(Token(inner, CLASS_LITERAL, line_no, "YARN"))
            tokens.append(Token('"', CLASS_STRING_DELIMITER, line_no))
            return tokens, errors, pos + 1
        pos += 1

    # unclosed string — emit whatever content was collected
    errors.append(LexError(line_no, text[start - 1:], "Unclosed string literal"))
    if start < n:
        tokens.append(Token(text[start:], CLASS_LITERAL, line_no, "YARN"))
    return tokens, errors, n


# tokenizes one statement line; indentation/extra spaces are ignored
# Sources: [CI-4] 4.3 (character-by-character scanning loop), [CORNELL-LEX] (contextual identifier vs keyword disambiguation).
def tokenize_fragment(text: str, line_no: int = 0) -> Tuple[List[Token], List[LexError]]:
    tokens: List[Token] = []
    errors: List[LexError] = []
    pos, n = 0, len(text)
    prev_kw = ""

    while pos < n:
        # spaces and tabs only separate lexemes; indentation is irrelevant
        if text[pos].isspace():
            pos += 1
            continue

        # YARN first: retain internal spaces; do not whitespace-split inside quotes
        if text[pos] == '"':
            yarn_toks, yarn_errs, pos = _scan_yarn(text, pos, line_no)
            tokens.extend(yarn_toks)
            errors.extend(yarn_errs)
            prev_kw = ""
            continue

        hit = match_lexeme_at(text, pos)
        if hit is None:
            end = pos
            while end < n and not text[end].isspace():
                end += 1
            errors.append(LexError(line_no, text[pos:end], "Unrecognized lexeme"))
            pos = end
            prev_kw = ""
            continue

        lexeme, cls, sub, name = hit
        # check if identifier is a function or loop name based on previous keyword
        if name == "IDENTIFIER":
            if prev_kw in _FUNC_CONTEXT:
                cls = CLASS_FUNC_IDENT
            elif prev_kw in _LOOP_CONTEXT:
                cls = CLASS_LOOP_IDENT

        tokens.append(Token(lexeme, cls, line_no, sub))
        # BTW starts a single-line comment: keep the keyword, strip the rest
        if name == "BTW":
            break
        prev_kw = name if cls not in (CLASS_VAR_IDENT, CLASS_FUNC_IDENT,
                                      CLASS_LOOP_IDENT, CLASS_LITERAL,
                                      CLASS_TYPE_LITERAL) else ""
        pos += len(lexeme)

    return tokens, errors


# true when the line's only lexeme is the given comment keyword (ignoring indent)
def _line_is_only_comment_keyword(line: str, keyword: str) -> bool:
    toks, errs = tokenize_fragment(line, 0)
    return not errs and len(toks) == 1 and toks[0].lexeme == keyword


# line-by-line scanner with BTW / OBTW ... TLDR comment handling
# Sources: [CI-4] 4.4 (comment stripping in lexical analysis), [TUT-LOL] (BTW inline and OBTW/TLDR block comments).
def tokenize_source(source: str) -> Tuple[List[Token], List[LexError]]:
    tokens: List[Token] = []
    errors: List[LexError] = []
    in_obtw = False
    obtw_line = 0

    # splitlines handles \n, \r\n, and \r; blank lines yield no tokens
    for line_no, line in enumerate(source.splitlines(), start=1):
        stripped = line.strip()

        # inside OBTW ... TLDR: skip body until a lone TLDR closes the block
        if in_obtw:
            if not stripped:
                continue
            hit = match_lexeme_at(stripped, 0)
            if hit and hit[3] == "TLDR":
                rest = stripped[len(hit[0]):].strip()
                if rest == "":
                    tokens.append(Token("TLDR", CLASS_COMMENT, line_no))
                    in_obtw = False
                else:
                    errors.append(LexError(
                        line_no, stripped,
                        "TLDR must occupy its own line and cannot coexist with other statements",
                    ))
            elif re.search(r"(?<![A-Za-z0-9_])TLDR(?![A-Za-z0-9_])", stripped):
                # TLDR appears mid-line with other text
                errors.append(LexError(
                    line_no, stripped,
                    "TLDR must occupy its own line and cannot coexist with other statements",
                ))
            # otherwise this line is comment body — ignore entirely
            continue

        if not stripped:
            continue

        # OBTW must be alone on its line; then enter multi-line comment state
        if _line_is_only_comment_keyword(line, "OBTW"):
            tokens.append(Token("OBTW", CLASS_COMMENT, line_no))
            in_obtw = True
            obtw_line = line_no
            continue

        # TLDR outside an OBTW block is invalid
        if _line_is_only_comment_keyword(line, "TLDR"):
            errors.append(LexError(
                line_no, "TLDR", "TLDR without matching OBTW",
            ))
            continue

        line_tokens, line_errors = tokenize_fragment(line, line_no)

        # reject OBTW/TLDR sharing a line with any other statement
        for t in line_tokens:
            if t.lexeme == "OBTW":
                errors.append(LexError(
                    line_no, line.strip(),
                    "OBTW must occupy its own line and cannot coexist with other statements",
                ))
                line_tokens = []
                line_errors = []
                break
            if t.lexeme == "TLDR":
                errors.append(LexError(
                    line_no, line.strip(),
                    "TLDR must occupy its own line and cannot coexist with other statements",
                ))
                line_tokens = []
                line_errors = []
                break

        tokens.extend(line_tokens)
        errors.extend(line_errors)

    if in_obtw:
        errors.append(LexError(
            obtw_line, "OBTW", "Unclosed multi-line comment (missing TLDR)",
        ))

    return tokens, errors


# reads a .lol file and runs the line-by-line scanner over its contents
# Sources: [CI-4] 4.1.1 (file loading and string scanning).
def tokenize_file(path: str) -> Tuple[List[Token], List[LexError]]:
    with open(path, encoding="utf-8") as f:
        return tokenize_source(f.read())


# prints a simple lexeme table for presentation / CLI use
# Sources: [WIKI-LEX] (tabular visualization of lexemes and token categories).
def print_lexeme_table(tokens: List[Token], errors: Optional[List[LexError]] = None) -> None:
    print(f"{'Line':<6}{'Lexeme':<30}Classification")
    print("-" * 60)
    for t in tokens:
        print(f"{t.line:<6}{t.lexeme:<30}{t.classification}")
    if errors:
        print()
        for e in errors:
            print(e, file=sys.stderr)


# runs test assertions to verify all lexeme patterns and classifications
# Sources: [CI-4] (lexer test coverage), [TUT-LOL] (syntax examples and test cases).
def _self_test() -> None:
    def kinds(src):
        toks, errs = tokenize_fragment(src, 1)
        return [(t.lexeme, t.classification) for t in toks], errs

    # code delimiter
    assert classify_lexeme("HAI") == ("Code Delimiter", "")
    assert classify_lexeme("KTHXBYE") == ("Code Delimiter", "")
    # declaration block delimiter
    assert classify_lexeme("WAZZUP") == ("Declaration Block Delimiter", "")
    assert classify_lexeme("BUHBYE") == ("Declaration Block Delimiter", "")
    # variable declaration
    assert classify_lexeme("I HAS A") == ("Variable Declaration", "")
    # variable initialization
    assert classify_lexeme("ITZ") == ("Variable Initialization", "")
    # assignment keyword
    assert classify_lexeme("R") == ("Assignment Keyword", "")
    # operand separator
    assert classify_lexeme("AN") == ("Operand Separator", "")
    # output keyword
    assert classify_lexeme("VISIBLE") == ("Output Keyword", "")
    # input keyword
    assert classify_lexeme("GIMMEH") == ("Input Keyword", "")
    # concatenation keyword
    assert classify_lexeme("SMOOSH") == ("Concatenation Keyword", "")
    # arithmetic operator
    for kw in ["SUM OF", "DIFF OF", "PRODUKT OF", "QUOSHUNT OF", "MOD OF", "BIGGR OF", "SMALLR OF"]:
        assert classify_lexeme(kw) == ("Arithmetic Operator", "")
    # comparison operator
    assert classify_lexeme("BOTH SAEM") == ("Comparison Operator", "")
    assert classify_lexeme("DIFFRINT") == ("Comparison Operator", "")
    # boolean operator
    for kw in ["BOTH OF", "EITHER OF", "WON OF", "NOT"]:
        assert classify_lexeme(kw) == ("Boolean Operator", "")
    # infinite arity operator
    assert classify_lexeme("ALL OF") == ("Infinite Arity Operator", "")
    assert classify_lexeme("ANY OF") == ("Infinite Arity Operator", "")
    # operator delimiter
    assert classify_lexeme("MKAY") == ("Operator Delimiter", "")
    # typecast keyword
    for kw in ["MAEK", "IS NOW A", "A"]:
        assert classify_lexeme(kw) == ("Typecast Keyword", "")
    # conditional keyword
    for kw in ["O RLY?", "YA RLY", "NO WAI", "MEBBE"]:
        assert classify_lexeme(kw) == ("Conditional Keyword", "")
    # switch-case keyword
    for kw in ["WTF?", "OMG", "OMGWTF"]:
        assert classify_lexeme(kw) == ("Switch-Case Keyword", "")
    # conditional and switch delimiter
    assert classify_lexeme("OIC") == ("Conditional/Switch Delimiter", "")
    # break keyword
    assert classify_lexeme("GTFO") == ("Break Keyword", "")
    # loop delimiter
    assert classify_lexeme("IM IN YR") == ("Loop Delimiter", "")
    assert classify_lexeme("IM OUTTA YR") == ("Loop Delimiter", "")
    # loop keyword
    for kw in ["UPPIN", "NERFIN", "TIL", "WILE"]:
        assert classify_lexeme(kw) == ("Loop Keyword", "")
    # function delimiter
    assert classify_lexeme("HOW IZ I") == ("Function Delimiter", "")
    assert classify_lexeme("IF U SAY SO") == ("Function Delimiter", "")
    # return keyword
    assert classify_lexeme("FOUND YR") == ("Return Keyword", "")
    # function call keyword
    assert classify_lexeme("I IZ") == ("Function Call Keyword", "")
    # parameter keyword
    assert classify_lexeme("YR") == ("Parameter Keyword", "")
    assert classify_lexeme("AN YR") == ("Parameter Keyword", "")
    # comment keyword
    for kw in ["BTW", "OBTW", "TLDR"]:
        assert classify_lexeme(kw) == (CLASS_COMMENT, "")
    # troof literal
    assert classify_lexeme("WIN") == (CLASS_LITERAL, "TROOF")
    assert classify_lexeme("FAIL") == (CLASS_LITERAL, "TROOF")
    # type literal
    for t_lit in ["NOOB", "NUMBR", "NUMBAR", "YARN", "TROOF"]:
        assert classify_lexeme(t_lit) == (CLASS_TYPE_LITERAL, "TYPE")
    # numbar literal
    for numbar in ["-3.5", "0.0", "42.125"]:
        assert classify_lexeme(numbar) == (CLASS_LITERAL, "NUMBAR")
    # numbr literal
    for numbr in ["-3", "0", "42"]:
        assert classify_lexeme(numbr) == (CLASS_LITERAL, "NUMBR")
    # variable identifier
    assert classify_lexeme("AN_ITEM") == (CLASS_VAR_IDENT, "")
    assert classify_lexeme("my_var123") == (CLASS_VAR_IDENT, "")
    # function identifier
    t, _ = kinds("HOW IZ I add YR x AN YR y")
    assert t[1] == ("add", CLASS_FUNC_IDENT) and t[3] == ("x", CLASS_VAR_IDENT)
    # loop identifier
    t, _ = kinds("IM IN YR loop UPPIN YR i")
    assert t[1] == ("loop", CLASS_LOOP_IDENT)
    # invalid literal
    assert classify_lexeme("+3") is None
    assert classify_lexeme("1.2.3") is None
    # lexical error
    t, e = kinds("VISIBLE 12abc @@")
    assert len(e) == 2 and e[0].lexeme == "12abc"

    # line-by-line scanner: newlines delimit statements; indentation ignored
    program = (
        "HAI 1.2\n"
        "    WAZZUP\n"
        "        I HAS A x ITZ 10\n"
        "    BUHBYE\n"
        "\n"
        "    VISIBLE x\n"
        "KTHXBYE\n"
    )
    toks, errs = tokenize_source(program)
    assert errs == []
    assert [t.line for t in toks] == [1, 1, 2, 3, 3, 3, 3, 4, 6, 6, 7]
    assert toks[0] == Token("HAI", "Code Delimiter", 1)
    assert toks[2] == Token("WAZZUP", "Declaration Block Delimiter", 2)
    assert toks[3].lexeme == "I HAS A" and toks[3].line == 3
    assert toks[5] == Token("ITZ", "Variable Initialization", 3)
    assert toks[6] == Token("10", CLASS_LITERAL, 3, "NUMBR")
    assert toks[8] == Token("VISIBLE", "Output Keyword", 6)
    assert toks[-1] == Token("KTHXBYE", "Code Delimiter", 7)
    # indented blank-separated lines still produce correct classifications
    assert [(t.lexeme, t.classification) for t in toks] == [
        ("HAI", "Code Delimiter"),
        ("1.2", CLASS_LITERAL),
        ("WAZZUP", "Declaration Block Delimiter"),
        ("I HAS A", "Variable Declaration"),
        ("x", CLASS_VAR_IDENT),
        ("ITZ", "Variable Initialization"),
        ("10", CLASS_LITERAL),
        ("BUHBYE", "Declaration Block Delimiter"),
        ("VISIBLE", "Output Keyword"),
        ("x", CLASS_VAR_IDENT),
        ("KTHXBYE", "Code Delimiter"),
    ]
    # errors keep the originating line number across the file
    bad = "HAI\nVISIBLE 12abc\nKTHXBYE\n"
    _, bad_errs = tokenize_source(bad)
    assert len(bad_errs) == 1 and bad_errs[0].line == 2 and bad_errs[0].lexeme == "12abc"

    # BTW: keep preceding statement; strip comment body after BTW
    btw = "VISIBLE x BTW this is ignored @@ junk\nKTHXBYE\n"
    toks, errs = tokenize_source(btw)
    assert errs == []
    assert [(t.lexeme, t.classification) for t in toks] == [
        ("VISIBLE", "Output Keyword"),
        ("x", CLASS_VAR_IDENT),
        ("BTW", CLASS_COMMENT),
        ("KTHXBYE", "Code Delimiter"),
    ]
    # BTW alone on a line still emits the keyword only
    toks, errs = tokenize_source("BTW just a comment\n")
    assert errs == [] and toks == [Token("BTW", CLASS_COMMENT, 1)]

    # OBTW ... TLDR: own lines; body is not tokenized
    obtw = (
        "HAI\n"
        "OBTW\n"
        "    this is a multi-line comment\n"
        "    VISIBLE should_not_appear\n"
        "TLDR\n"
        "VISIBLE x\n"
        "KTHXBYE\n"
    )
    toks, errs = tokenize_source(obtw)
    assert errs == []
    assert [(t.lexeme, t.classification, t.line) for t in toks] == [
        ("HAI", "Code Delimiter", 1),
        ("OBTW", CLASS_COMMENT, 2),
        ("TLDR", CLASS_COMMENT, 5),
        ("VISIBLE", "Output Keyword", 6),
        ("x", CLASS_VAR_IDENT, 6),
        ("KTHXBYE", "Code Delimiter", 7),
    ]
    # OBTW cannot share a line with other statements
    _, errs = tokenize_source("OBTW trailing text\nTLDR\n")
    assert any("OBTW must occupy its own line" in e.message for e in errs)
    _, errs = tokenize_source("VISIBLE OBTW\n")
    assert any("OBTW must occupy its own line" in e.message for e in errs)
    # TLDR cannot share a line with other statements
    _, errs = tokenize_source("OBTW\nTLDR trailing\n")
    assert any("TLDR must occupy its own line" in e.message for e in errs)
    # TLDR without OBTW
    _, errs = tokenize_source("TLDR\n")
    assert any("TLDR without matching OBTW" in e.message for e in errs)
    # unclosed OBTW
    _, errs = tokenize_source("OBTW\nstill commenting\n")
    assert any("Unclosed multi-line comment" in e.message for e in errs)

    # YARN: quotes are String Delimiter; inner text is Literal (spaces kept)
    t, e = kinds('VISIBLE "Hai world!"')
    assert e == []
    assert t == [
        ("VISIBLE", "Output Keyword"),
        ('"', CLASS_STRING_DELIMITER),
        ("Hai world!", CLASS_LITERAL),
        ('"', CLASS_STRING_DELIMITER),
    ]
    yarn_toks, _ = tokenize_fragment('"Hai world!"', 1)
    assert yarn_toks[1].subtype == "YARN"
    # empty YARN
    t, e = kinds('""')
    assert e == [] and t == [
        ('"', CLASS_STRING_DELIMITER),
        ("", CLASS_LITERAL),
        ('"', CLASS_STRING_DELIMITER),
    ]
    # escaped quote :\" stays inside the literal
    t, e = kinds('"say :"hi:""')
    assert e == []
    assert t[1] == ('say :"hi:"', CLASS_LITERAL)
    # BTW inside a YARN is not a comment
    toks, errs = tokenize_source('VISIBLE "BTW not a comment"\n')
    assert errs == []
    assert [x.lexeme for x in toks] == ["VISIBLE", '"', "BTW not a comment", '"']
    # unclosed YARN
    _, e = kinds('VISIBLE "oops')
    assert any("Unclosed string literal" in err.message for err in e)

    print("lol_lexemes self-test: OK")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        path = sys.argv[1]
        toks, errs = tokenize_file(path)
        print_lexeme_table(toks, errs)
        sys.exit(1 if errs else 0)
    _self_test()
