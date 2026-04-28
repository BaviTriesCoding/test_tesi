import * as React from "react";
const { useState, useEffect, useContext } = React;
import { useRpcSession, EditorContext } from "@leanprover/infoview";

// ──────────────────────────────────────────────────────────────────
// Natural Deduction Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

// Gap in px between sibling premise subtrees
const PREMISE_GAP = 16;

function NDTreeNode({ node, depth = 0 }) {
  if (!node) return null;

  const isLeaf      = !node.children || node.children.length === 0;
  const isClosed    = node.isDischarged === false;
  const isUnhandled = !!node.isUnhandled;

  const formulaText = node.formula ?? "?";
  const displayText = isLeaf && isClosed ? `[${formulaText}]` : formulaText;

  const formulaColor = isUnhandled ? "#f0a050" : "#d4d4d4";
  const formulaStyle = {
    color: formulaColor,
    whiteSpace: "nowrap",
    fontSize: "13px",
    fontFamily: "monospace",
    padding: "1px 2px",
  };

  // ── LEAF: no bar, just the formula (possibly bracketed / highlighted)
  if (isLeaf) {
    return React.createElement(
      "div",
      {
        style: {
          display: "inline-block",
          textAlign: "center",
          verticalAlign: "bottom",
          ...(isUnhandled && {
            outline: "1px dashed #f0a050",
            borderRadius: "2px",
            padding: "1px 3px",
          }),
        },
      },
      React.createElement("span", { style: formulaStyle }, displayText),
      isUnhandled
        ? React.createElement(
            "div",
            {
              style: {
                fontSize: "9px",
                color: "#f0a050",
                letterSpacing: "0.05em",
                marginTop: "1px",
              },
            },
            "⚠ unhandled",
          )
        : null,
    );
  }

  // ── INTERNAL NODE
  //
  // display:inline-block → the node width = max(children_row, conclusion).
  // The bar wrapper uses width:100% to always span that max.
  // The rule label is position:absolute so it never inflates the node width.
  return React.createElement(
    "div",
    {
      style: {
        display: "inline-block",
        textAlign: "center",
        verticalAlign: "bottom",
      },
    },

    // ── children row (inline-flex → shrink-wraps to exact content width)
    React.createElement(
      "div",
      {
        style: {
          display: "inline-flex",
          justifyContent: "center",
          alignItems: "flex-end",
          gap: `${PREMISE_GAP}px`,
          whiteSpace: "nowrap",
        },
      },
      node.children.map((p, i) =>
        React.createElement(NDTreeNode, { key: i, node: p, depth: depth + 1 }),
      ),
    ),

    // ── Bar + rule label
    React.createElement(
      "div",
      {
        style: {
          position: "relative",
          margin: "5px 0 3px 0",
          width: "100%",
        },
      },
      // Horizontal rule — always as wide as the inline-block container
      React.createElement("div", {
        style: {
          borderTop: isUnhandled
            ? "1.5px dashed #f0a050"
            : "1.5px solid #858585",
          width: "100%",
        },
      }),
      // Rule label: absolute, right of the bar, never affects layout
      node.rule
        ? React.createElement(
            "span",
            {
              style: {
                position: "absolute",
                left: "calc(100% + 8px)",
                top: "50%",
                transform: "translateY(-50%)",
                color: isUnhandled ? "#f0a050" : "#9cdcfe",
                fontSize: "11px",
                fontStyle: "italic",
                whiteSpace: "nowrap",
                userSelect: "none",
              },
            },
            isUnhandled ? `⚠ ${node.rule}` : node.rule,
          )
        : null,
    ),

    // ── Conclusion formula
    React.createElement(
      "div",
      { style: { display: "inline-block", whiteSpace: "nowrap" } },
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

  const [result, setResult]           = useState(null);
  const [error, setError]             = useState(null);
  const [showRaw, setShowRaw]         = useState(false);
  const [copySuccess, setCopySuccess] = useState(false);

  useEffect(() => {
    const pos = props.pos;
    if (!pos || !rs) return;
    setError(null);
    rs.call("getTreeAsJson", { pos })
      .then((res) => {
        const validJSON = res.treeJson.replace(/[\x00-\x1F\x7F-\x9F]/g, "");
        const tree = JSON.parse(validJSON);
        setResult({ name: res.thmName, type: res.thmType, tree, treeJson: res.treeJson });
        setCopySuccess(false);
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
    console.log("Fetching NDTree for position", pos);
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

    // ── Header
    React.createElement(
      "div",
      { style: headerStyle },
      React.createElement(
        "span",
        { style: { color: "#9cdcfe", fontWeight: "bold" } },
        result.name,
      ),
      React.createElement("span", { style: { color: "#858585" } }, " : "),
      React.createElement("span", { style: { color: "#ce9178" } }, result.type),
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

    // ── Buttons
    React.createElement(
      "div",
      { style: { marginBottom: "8px" } },
      React.createElement(
        "button",
        {
          style: { ...buttonStyle, background: showRaw ? "#0e639c" : "#2d2d30" },
          onClick: () => setShowRaw(!showRaw),
        },
        showRaw ? "🌲 Vista Albero" : "📄 Vista Raw JSON",
      ),
      !showRaw &&
        React.createElement(
          "button",
          { style: buttonStyle, onClick: copyToClipboard },
          copySuccess ? "✓ Copiato!" : "📋 Copia JSON",
        ),
    ),

    // ── Content
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
      : // ── Tree view
        // FIX for left-overflow scroll bug:
        // Using overflow-x:auto on a block container with text-align:center
        // and the tree as an inline-block child.
        // This works correctly because the scrollable area expands in BOTH
        // directions when the inline-block overflows, unlike flex+justify-center
        // which clips the left side and makes it un-scrollable.
        React.createElement(
          "div",
          {
            style: {
              background: "#1a1a1a",
              border: "1px solid #3c3c3c",
              borderRadius: "3px",
              padding: "24px 80px 16px 16px", // extra right padding for rule labels
              overflowX: "auto",
              overflowY: "auto",
              maxHeight: "500px",
              // Use text-align:center so the inline-block tree centres, but
              // overflow in both directions stays scrollable.
              textAlign: "center",
              whiteSpace: "nowrap",
            },
          },
          React.createElement(
            "div",
            {
              style: {
                // inline-block so text-align:center applies and the div
                // shrink-wraps to the tree content (enabling correct scroll)
                display: "inline-block",
                textAlign: "left",
              },
            },
            React.createElement(NDTreeNode, { node: result.tree }),
          ),
        ),
  );
}