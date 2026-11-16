import { useEffect, useRef, useState } from "react";

// ------------------------------------------------------------ state management
export default function App() {
  const [fileName, setFileName] = useState("(None)");
  const [files, setFiles] = useState([]);
  const [menu, setMenu] = useState(false);
  const [code, setCode] = useState("");
  const [tokens, setTokens] = useState([]);
  const [symbols, setSymbols] = useState([]);
  const [lines, setLines] = useState([]);
  const [badLines, setBadLines] = useState(new Set());
  const [running, setRunning] = useState(false);
  const [asking, setAsking] = useState(false);
  const [answer, setAnswer] = useState("");
  const ws = useRef(null);
  const gutter = useRef(null);
  const picker = useRef(null);
  const answerBox = useRef(null);
  const consoleEnd = useRef(null);

  // initial data loading
  useEffect(() => {
    fetch("/api/files").then((r) => r.json()).then(setFiles).catch(() => {});
  }, []);
  // automatic console scrolling
  useEffect(() => {
    consoleEnd.current?.scrollIntoView({ block: "end" });
  }, [lines, asking]);
  // automatic input field focus
  useEffect(() => { if (asking) answerBox.current?.focus(); }, [asking]);
 
  // console message handler
  const log = (kind, text) => setLines((l) => [...l.slice(-4999), { kind, text }]);

  // ------------------------------------------------------------ file management
  const openServerFile = async (name) => {
    setMenu(false);
    const r = await fetch(`/api/files/${encodeURIComponent(name)}`);
    const data = await r.json();
    setCode(data.content);
    setFileName(data.name);
  };

  // local file import
  const openLocalFile = async (e) => {
    const f = e.target.files[0];
    if (!f) return;
    setMenu(false);
    setCode(await f.text());
    setFileName(f.name);
    e.target.value = "";
  };

  // ------------------------------------------------------------ websocket message handler
  const handle = (m, sock) => {
    switch (m.type) {
      case "tokens": setTokens(m.tokens); break;
      case "symbols": setSymbols(m.symbols); break;
      case "output": log("out", m.text.replace(/\n$/, "")); break;
      case "input_request": setAsking(true); break;
      case "issues":
        m.issues.forEach((i) => log(i.severity, `${i.category} ${i.severity} (line ${i.line}): ${i.message}`));
        setBadLines(new Set(m.issues.filter((i) => i.severity === "error").map((i) => i.line)));
        break;
      case "stopped": log("info", "Program stopped."); break;
      case "fatal": log("error", `Interpreter crashed: ${m.message}`); break;
      case "done": sock.finished = true; setRunning(false); setAsking(false); sock.close(); break;
      default: break;
    }
  };

  // ------------------------------------------------------------ program execution
  const run = () => {
    setTokens([]); setSymbols([]); setLines([]); setBadLines(new Set());
    setRunning(true);

    // Establishes a WebSocket connection
    // Uses wss for HTTPS and ws for HTTP connections
    const sock = new WebSocket(`${location.protocol === "https:" ? "wss" : "ws"}://${location.host}/ws`);

    ws.current = sock;
    sock.onopen = () => sock.send(JSON.stringify({ type: "run", source: code, delay: 0 }));
    sock.onmessage = (e) => handle(JSON.parse(e.data), sock);
    sock.onerror = () => {
      if (sock.finished) return;
      log("error", "Cannot reach the Python server. Start it with: python server.py");
      setRunning(false);
    };
  };

  const stop = () => ws.current?.send(JSON.stringify({ type: "stop" }));

  const submitAnswer = (e) => {
    e.preventDefault();
    ws.current.send(JSON.stringify({ type: "input", value: answer }));
    log("in", answer);
    setAnswer("");
    setAsking(false);
  };

  return (
    <div className="window">
      {/* file explorer */}
      <div className="explorer">
        
        <button className="folder" onClick={() => setMenu(!menu)} title="Open a LOLCODE file">
          Open file
        </button>
        <span className="fname">{fileName}</span>
        {menu && (
          <ul className="menu">
            {files.map((f) => <li key={f}><button onClick={() => openServerFile(f)}>{f}</button></li>)}
            <li><button onClick={() => picker.current.click()}>Browse this computer…</button></li>
          </ul>
        )}
        <input ref={picker} type="file" accept=".lol,.txt" hidden onChange={openLocalFile} />
      </div>
      
      {/* main interface */}
      <main className="panes">
        {/* text editor */}
        <section className="pane editor-pane">
          <h2>Text editor</h2>
          <div className="editor">
            <div className="gutter" ref={gutter}>
              {code.split("\n").map((_, i) => (
                <div key={i} className={badLines.has(i + 1) ? "bad" : ""}>{i + 1}</div>
              ))}
            </div>
            <textarea
              value={code}
              spellCheck={false}
              wrap="off"
              placeholder="Open a file, or type LOLCODE here…"
              onChange={(e) => setCode(e.target.value)}
              onScroll={(e) => { gutter.current.scrollTop = e.target.scrollTop; }}
            />
          </div>
        </section>
        
        {/* lexemes table */}
        <section className="pane">
          <h2>Lexemes</h2>
          <div className="scroll">
            <table>
              <thead><tr><th>Lexeme</th><th>Classification</th></tr></thead>
              <tbody>
                {tokens.map((t, i) => (
                  <tr key={i}>
                    <td className="mono">{t.lexeme === "" ? <em>(empty)</em> : t.lexeme}</td>
                    <td>{t.classification}</td>
                  </tr>
                ))}
              </tbody>
            </table>
            {!tokens.length && <p className="empty">Press Execute to list the lexemes.</p>}
          </div>
        </section>
        
        {/* symbol table */}
        <section className="pane">
          <h2>Symbol table</h2>
          <div className="scroll">
            <table>
              <thead><tr><th>Identifier</th><th>Value</th></tr></thead>
              <tbody>
                {symbols.map((s) => (
                  <tr key={s.name}>
                    <td className="mono">{s.name}</td>
                    <td key={s.value} className="mono pulse">
                      {s.value} <small>{s.type}</small>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
            {!symbols.length && <p className="empty">Variables appear here as the program runs.</p>}
          </div>
        </section>
      </main>
      
      {/* execute/stop botton */}
      <button className={`execute ${running ? "stop" : ""}`} onClick={running ? stop : run}>
        {running ? "Stop" : "Execute"}
      </button>
      
      {/* console */}
      <section className="console">
        <h2>Console</h2>
        <div className="log">
          {lines.map((l, i) => <div key={i} className={`line ${l.kind}`}>{l.text}</div>)}
          {/* user input prompt */}
          {asking && (
            <form className="ask" onSubmit={submitAnswer}>
              <span>GIMMEH ›</span>
              <input ref={answerBox} value={answer} onChange={(e) => setAnswer(e.target.value)} />
            </form>
          )}
          <div ref={consoleEnd} />
        </div>
      </section>
    </div>
  );
}
