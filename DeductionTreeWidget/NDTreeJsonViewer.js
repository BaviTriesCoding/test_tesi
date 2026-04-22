import * as React from "react";
const { useState, useEffect, useContext } = React;
import { useRpcSession, EditorContext } from "@leanprover/infoview";

// ──────────────────────────────────────────────────────────────────
// Natural Deduction Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

function NDTreeNode({ node, depth = 0 }) {
  if (!node) return null;

  const isLeaf = !node.premises || node.premises.length === 0;
  const isClosed = node.isOpen === false;

  const formulaText = node.formula ?? "?";
  const displayText = isLeaf && isClosed ? `[${formulaText}]` : formulaText;

  const formulaStyle = {
    color: "#d4d4d4",
    whiteSpace: "nowrap",
    fontSize: "13px",
    fontFamily: "monospace",
    padding: "1px 2px",
  };

  // ── Leaf node: no bar, just the formula (possibly bracketed)
  if (isLeaf) {
    return React.createElement(
      "div",
      {
        style: {
          display: "inline-block",
          textAlign: "center",
          verticalAlign: "bottom",
          padding: "0 8px",
        },
      },
      React.createElement("span", { style: formulaStyle }, displayText),
    );
  }

  // ── Internal node: premises / bar+rule / formula
  return React.createElement(
    "div",
    {
      style: {
        display: "inline-block",
        textAlign: "center",
        verticalAlign: "bottom",
        padding: "0 8px",
      },
    },

    // ── Premises row (aligned at baseline / bottom)
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          justifyContent: "center",
          alignItems: "flex-end",
          gap: "2px",
        },
      },
      node.premises.map((p, i) =>
        React.createElement(NDTreeNode, { key: i, node: p, depth: depth + 1 }),
      ),
    ),

    // ── Horizontal bar + rule name (absolutely positioned so it doesn't
    //    affect the bar width and the formula stays centered)
    React.createElement(
      "div",
      {
        style: {
          position: "relative",   // anchor for the absolute rule label
          margin: "5px 0 3px 0",
        },
      },
      // The bar itself spans 100 % of the container width
      React.createElement("div", {
        style: {
          borderTop: "1.5px solid #858585",
          width: "100%",
          minWidth: "30px",
        },
      }),
      // Rule label floats outside to the right, vertically centred on the bar
      node.rule
        ? React.createElement(
            "span",
            {
              style: {
                position: "absolute",
                left: "calc(100% + 10px)",   // 10 px gap from bar end
                top: "50%",
                transform: "translateY(-50%)",
                color: "#9cdcfe",
                fontSize: "11px",
                fontStyle: "italic",
                whiteSpace: "nowrap",
                userSelect: "none",
              },
            },
            node.rule,
          )
        : null,
    ),

    // ── formula
    React.createElement(
      "div",
      { style: { display: "flex", justifyContent: "center" } },
      React.createElement("span", { style: formulaStyle }, displayText),
    ),
  );
}

// ──────────────────────────────────────────────────────────────────
// Main Widget
// ──────────────────────────────────────────────────────────────────

export default function NDTreeViewer(props) {
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
      "⚠ RpcContext non disponibile",
    );

  if (error)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#f44747" } },
      "⚠ ",
      error,
    );

  if (!result)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#858585" } },
      "Sposta il cursore su un teorema per visualizzare l'NDTree...",
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

    // ── Header: theorem name and type
    React.createElement(
      "div",
      { style: headerStyle },
      React.createElement(
        "span",
        { style: { color: "#9cdcfe", fontWeight: "bold" } },
        result.name,
      ),
      React.createElement("span", { style: { color: "#858585" } }, " : "),
      React.createElement(
        "span",
        { style: { color: "#ce9178" } },
        result.type,
      ),
    ),

    // ── Subtitle
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
      "ALBERO DI DEDUZIONE NATURALE",
    ),

    // ── Toggle button
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
        showRaw ? "🌲 Vista Albero" : "📄 Vista Raw JSON",
      ),
      !showRaw &&
        React.createElement(
          "button",
          {
            style: buttonStyle,
            onClick: copyToClipboard,
          },
          copySuccess ? "✓ Copiato!" : "📋 Copia JSON",
        ),
    ),

    // ── Content: tree or raw JSON
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
              maxHeight: "500px",
              overflowY: "auto",
            },
          },
          JSON.stringify(result.tree, null, 2),
        )
      : React.createElement(
          "div",
          {
            style: {
              background: "#1a1a1a",
              border: "1px solid #3c3c3c",
              borderRadius: "3px",
              padding: "16px",
              overflowX: "auto",
              overflowY: "auto",
              maxHeight: "500px",
              // Centre the whole tree horizontally
              display: "flex",
              justifyContent: "center",
              alignItems: "flex-end",
            },
          },
          React.createElement(NDTreeNode, { node: result.tree }),
        ),
  );
}