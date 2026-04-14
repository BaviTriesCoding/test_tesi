import * as React from "react";
const { useState, useEffect, useRef, useContext } = React;

// ── Import corretto per l'RPC nei widget Lean nativi ─────────────
import { useRpcSession, EditorContext } from "@leanprover/infoview";

export default function JsonViewer(props) {
  const rs = useRpcSession();
  const [result, setResult] = useState(null);
  const [error, setError] = useState(null);
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    const pos = props.pos;
    if (!pos || !rs) return;
    setError(null);
    rs.call("getDeductionAtCursor", { pos })
      .then((res) => {
        setResult(JSON.stringify(res, null, 2));
        setLoading(false);
      })
      .catch((err) => {
        setError(err.message || "Unknown error");
        setLoading(false);
      });
  }, [props.pos, rs]);

  const containerStyle = {
    fontFamily: "monospace",
    fontSize: "12px",
    color: "#efefef",
    backgroundColor: "#1e1e1e",
    padding: "10px",
    borderRadius: "4px",
    overflowX: "auto",
  };

  return (
    <div style={containerStyle}>
      {loading && "Loading..."}
      {error && <span style={{ color: "red" }}>{error}</span>}
      {result && <pre>{result}</pre>}
    </div>
  );
}