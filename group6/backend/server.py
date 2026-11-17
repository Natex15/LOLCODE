# BACKEND FRAMEWORK: FLASK

import json, os, queue, threading, time
from flask import Flask, abort, jsonify
from flask_sock import Sock
import lol_semantics as sem
from lol_lexemes import tokenize_source

 # ------------------------------------------------------------ setup
 # Defines the directory containing the saved LOL source files
PROGRAMS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "programs")
app = Flask(__name__)
sock = Sock(app)

# Custom exception raised when program execution is stopped
class Stopped(Exception):
    pass

# Manages an individual WebSocket execution session
class Session:
    def __init__(self, ws):
        self.ws, self.inbox, self.lock = ws, queue.Queue(), threading.Lock()
        self.stop, self.delay, self.last = False, 0.0, None

    def send(self, **msg):
        with self.lock:
            self.ws.send(json.dumps(msg))

    #  Sends the current symbol table to the frontend.
    # (Option B) push the table whenever a value changed
    def symbols(self, sa):  
        rows = [{"name": s.name, "type": s.type, "value": sem._format_symbol_value(s)}
                for s in sa.globals.values()]
        if rows != self.last:
            self.last = rows
            self.send(type="symbols", symbols=rows)

 # ------------------------------------------------------------ program execution
def run(s, source):
    try:
        # Tokenization
        # (Option B) token list is sent once
        tokens, _ = tokenize_source(source)  
        s.send(type="tokens", tokens=[{"lexeme": t.lexeme, "classification": t.classification,
                                       "line": t.line} for t in tokens])

        def out(text):
            if s.stop:
                raise Stopped()
            s.send(type="output", text=str(text) + "\n")

        def inp():
            s.send(type="input_request")
            v = s.inbox.get()
            if v is None:
                raise Stopped()
            return v

        # STATEMENT EXECUTION CALLBACK (hook in lol_semantics.py)
        # Handles actions performed after each statement
        def on_statement(sa):  
            if s.stop:
                raise Stopped()
            s.symbols(sa)
            if s.delay:
                time.sleep(s.delay)

        issues, sa = sem.analyze_source(source, input_fn=inp, output_fn=out, on_statement=on_statement)
        if s.last is not None:
            s.symbols(sa)
        s.send(type="issues", issues=[{"line": i.line, "severity": i.severity,
                                       "category": i.category, "message": i.message} for i in issues])
    except Stopped:
        s.send(type="stopped")
    except Exception as e:
        s.send(type="fatal", message=repr(e))
    finally:
        s.send(type="done")


 # ------------------------------------------------------------ WebSocket route
@sock.route("/ws")
def ws(ws):
    s, thread = Session(ws), None
    try:
        while True:
            raw = ws.receive()
            if raw is None:
                break
            m = json.loads(raw)
            if m["type"] == "run" and not (thread and thread.is_alive()):
                s.stop, s.last, s.delay = False, None, float(m.get("delay", 0))
                thread = threading.Thread(target=run, args=(s, m["source"]), daemon=True)
                thread.start()
            elif m["type"] == "input":
                s.inbox.put(m["value"])
            elif m["type"] == "stop":
                s.stop = True
                s.inbox.put(None)
    finally:
        s.stop = True
        s.inbox.put(None)


@app.get("/api/files")
def files():
    return jsonify(sorted(f for f in os.listdir(PROGRAMS) if f.endswith(".lol")))


@app.get("/api/files/<name>")
def get_file(name):
    path = os.path.join(PROGRAMS, os.path.basename(name))
    if not os.path.isfile(path):
        abort(404)
    with open(path, encoding="utf-8") as f:
        return jsonify(name=name, content=f.read())


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, threaded=True)
