import React from "react";
import { createRoot } from "react-dom/client";
import App from "./App.jsx";
import "./styles.css";

class Boundary extends React.Component {
  state = { error: null };
  static getDerivedStateFromError(error) { return { error }; }
  render() {
    if (!this.state.error) return this.props.children;
    return (
      <div style={{ padding: 24, fontFamily: "monospace" }}>
        <h3 style={{ color: "#c2271d" }}>The page crashed</h3>
        <pre style={{ whiteSpace: "pre-wrap" }}>{String(this.state.error.stack || this.state.error)}</pre>
        <button onClick={() => location.reload()}>Reload</button>
      </div>
    );
  }
}

createRoot(document.getElementById("root")).render(<Boundary><App /></Boundary>);
