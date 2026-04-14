import * as React from "react";
const { useState, useEffect, useContext } = React;
import { useRpcSession, EditorContext } from "@leanprover/infoview";

// ──────────────────────────────────────────────────────────────────
// JSON Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

function JsonNode({ data, path = "", depth = 0 }) {
  const [expanded, setExpanded] = useState(depth < 2);

  if (data === null) {
    return React.createElement(
      "span",
      { style: { color: "#858585" } },
      "null"
    );
  }

  if (typeof data === "boolean") {
    return React.createElement(
      "span",
      { style: { color: "#569cd6" } },
      data.toString()
    );
  }

  if (typeof data === "number") {
    return React.createElement(
      "span",
      { style: { color: "#b5cea8" } },
      data.toString()
    );
  }

  if (typeof data === "string") {
    return React.createElement(
      "span",
      { style: { color: "#ce9178" } },
      `"${data}"`
    );
  }

  // Array
  if (Array.isArray(data)) {
    const isEmpty = data.length === 0;
    return React.createElement(
      "div",
      null,
      React.createElement(
        "span",
        {
          onClick: !isEmpty ? () => setExpanded((e) => !e) : undefined,
          style: {
            cursor: !isEmpty ? "pointer" : "default",
            userSelect: "none",
            color: "#858585",
          },
        },
        !isEmpty ? (expanded ? "▾" : "▸") : "·",
        " [ ",
        isEmpty ? " ]" : ""
      ),
      expanded && !isEmpty
        ? React.createElement(
            "div",
            { style: { marginLeft: "20px" } },
            data.map((item, idx) =>
              React.createElement(
                "div",
                { key: idx, style: { marginBottom: "3px" } },
                React.createElement(
                  "span",
                  { style: { color: "#858585" } },
                  `[${idx}]: `
                ),
                React.createElement(JsonNode, {
                  data: item,
                  path: `${path}[${idx}]`,
                  depth: depth + 1,
                })
              )
            ),
            React.createElement(
              "span",
              { style: { color: "#858585" } },
              "]"
            )
          )
        : null
    );
  }

  // Object
  if (typeof data === "object") {
    const keys = Object.keys(data);
    const isEmpty = keys.length === 0;
    return React.createElement(
      "div",
      null,
      React.createElement(
        "span",
        {
          onClick: !isEmpty ? () => setExpanded((e) => !e) : undefined,
          style: {
            cursor: !isEmpty ? "pointer" : "default",
            userSelect: "none",
            color: "#858585",
          },
        },
        !isEmpty ? (expanded ? "▾" : "▸") : "·",
        " { ",
        isEmpty ? " }" : ""
      ),
      expanded && !isEmpty
        ? React.createElement(
            "div",
            { style: { marginLeft: "20px" } },
            keys.map((key) =>
              React.createElement(
                "div",
                { key, style: { marginBottom: "3px" } },
                React.createElement(
                  "span",
                  { style: { color: "#9cdcfe" } },
                  `"${key}"`
                ),
                React.createElement("span", { style: { color: "#858585" } }, ": "),
                React.createElement(JsonNode, {
                  data: data[key],
                  path: `${path}.${key}`,
                  depth: depth + 1,
                })
              )
            ),
            React.createElement(
              "span",
              { style: { color: "#858585" } },
              "}"
            )
          )
        : null
    );
  }

  return React.createElement("span", null, String(data));
}

// ──────────────────────────────────────────────────────────────────
// Main Widget
// ──────────────────────────────────────────────────────────────────

export default function NDTreeJsonViewer(props) {
  const rs = useRpcSession();
  const ec = useContext(EditorContext);

  const [result, setResult] = useState(null);
  const [error, setError] = useState(null);
  const [showRaw, setShowRaw] = useState(false);
  const [copySuccess, setCopySuccess] = useState(false);

  useEffect(() => {
    const pos = props.pos;
    if (!pos || !rs) return;
    setError(null);
    rs.call("getTreeAsJson", { pos })
      .then((res) => {
        const tree = JSON.parse(res.treeJson);
        setResult({
          name: res.thmName,
          type: res.thmType,
          tree,
          treeJson: res.treeJson,
        });
        setCopySuccess(false);
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
  }, [props.pos, rs]);

  const containerStyle = {
    background: "#1e1e1e",
    color: "#d4d4d4",
    padding: "12px",
    fontFamily: "monospace",
    fontSize: "12px",
    minHeight: "60px",
    overflowX: "auto",
  };

  const headerStyle = {
    borderBottom: "1px solid #3c3c3c",
    marginBottom: "10px",
    paddingBottom: "6px",
  };

  const buttonStyle = {
    background: "#2d2d30",
    border: "1px solid #3c3c3c",
    color: "#d4d4d4",
    padding: "4px 8px",
    marginRight: "6px",
    marginBottom: "8px",
    borderRadius: "3px",
    cursor: "pointer",
    fontSize: "11px",
    userSelect: "none",
  };

  if (!rs)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#f44747" } },
      "⚠ RpcContext non disponibile"
    );

  if (error)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#f44747" } },
      "⚠ ",
      error
    );

  if (!result)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#858585" } },
      "Sposta il cursore su un teorema per visualizzare l'NDTree in JSON..."
    );

  const copyToClipboard = () => {
    navigator.clipboard.writeText(result.treeJson).then(() => {
      setCopySuccess(true);
      setTimeout(() => setCopySuccess(false), 2000);
    });
  };

  return React.createElement(
    "div",
    { style: containerStyle },
    // Intestazione
    React.createElement(
      "div",
      { style: headerStyle },
      React.createElement(
        "span",
        { style: { color: "#9cdcfe", fontWeight: "bold" } },
        result.name
      ),
      React.createElement("span", { style: { color: "#858585" } }, " : "),
      React.createElement("span", { style: { color: "#ce9178" } }, result.type)
    ),
    // Sottotitolo
    React.createElement(
      "div",
      {
        style: {
          color: "#858585",
          marginBottom: "8px",
          fontSize: "11px",
          letterSpacing: "0.05em",
        },
      },
      "TREE IN JSON"
    ),
    // Pulsanti di controllo
    React.createElement(
      "div",
      { style: { marginBottom: "8px" } },
      React.createElement(
        "button",
        {
          style: {
            ...buttonStyle,
            background: showRaw ? "#0e639c" : "#2d2d30",
          },
          onClick: () => setShowRaw(!showRaw),
        },
        showRaw ? "📋 Vista Albero" : "📄 Vista Raw JSON"
      ),
      React.createElement(
        "button",
        {
          style: buttonStyle,
          onClick: copyToClipboard,
        },
        copySuccess ? "✓ Copiato!" : "📋 Copia JSON"
      )
    ),
    // Contenuto
    showRaw
      ? React.createElement(
          "div",
          {
            style: {
              background: "#1a1a1a",
              border: "1px solid #3c3c3c",
              borderRadius: "3px",
              padding: "8px",
              overflowX: "auto",
              fontSize: "11px",
              lineHeight: "1.5",
              color: "#ce9178",
              whiteSpace: "pre-wrap",
              wordBreak: "break-word",
              maxHeight: "400px",
              overflowY: "auto",
            },
          },
          JSON.stringify(result.tree, null, 2)
        )
      : React.createElement(
          "div",
          {
            style: {
              background: "#1a1a1a",
              border: "1px solid #3c3c3c",
              borderRadius: "3px",
              padding: "8px",
              overflowX: "auto",
              maxHeight: "400px",
              overflowY: "auto",
            },
          },
          React.createElement(JsonNode, { data: result.tree })
        )
  );
}
