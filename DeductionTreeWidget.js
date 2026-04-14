import * as React from "react";
const { useState, useEffect, useRef, useContext } = React;

// ── Import corretto per l'RPC nei widget Lean nativi ─────────────
import { useRpcSession, EditorContext } from "@leanprover/infoview";

// ── Colori per tipo di nodo ───────────────────────────────────────
const NODE_COLORS = {
  hyp: { border: "#4ec9b0", bg: "#0d2b26", label: "#4ec9b0", tag: "HYP" },
  axiom: { border: "#dcdcaa", bg: "#2a2810", label: "#dcdcaa", tag: "AX" },
  lam: { border: "#c586c0", bg: "#2a1a2a", label: "#c586c0", tag: "→I" },
  forall: { border: "#c586c0", bg: "#2a1a2a", label: "#c586c0", tag: "∀I" },
  app: { border: "#569cd6", bg: "#0d1e2e", label: "#569cd6", tag: "→E" },
  sorry: { border: "#f44747", bg: "#2e0d0d", label: "#f44747", tag: "⚠" },
};

// ── Singolo nodo collassabile ─────────────────────────────────────
function TreeNode({ node, depth }) {
  const [open, setOpen] = useState(true);
  if (!node) return null;

  const col = NODE_COLORS[node.kind] ?? NODE_COLORS.sorry;
  const hasChildren = node.sub || node.fun || node.arg;

  const label =
    node.kind === "hyp"
      ? node.name + " : " + node.type
      : node.kind === "axiom"
        ? node.name + " : " + node.type
        : node.kind === "lam"
          ? "assume " + node.name + " : " + node.type
          : node.kind === "forall"
            ? "∀ " + node.name + " : " + node.type
            : node.kind === "app"
              ? ": " + node.type
              : "⚠ prova incompleta : " + node.type;

  return React.createElement(
    "div",
    {
      style: { marginLeft: depth * 20 + "px", marginBottom: "4px" },
    },
    React.createElement(
      "div",
      {
        onClick: hasChildren ? () => setOpen((o) => !o) : undefined,
        style: {
          display: "inline-flex",
          alignItems: "center",
          gap: "6px",
          background: col.bg,
          border: "1px solid " + col.border,
          borderRadius: "4px",
          padding: "2px 8px",
          cursor: hasChildren ? "pointer" : "default",
          userSelect: "none",
          maxWidth: "580px",
          flexWrap: "wrap",
          fontFamily: "monospace",
          fontSize: "12px",
        },
      },
      hasChildren
        ? React.createElement(
            "span",
            { style: { color: "#858585", fontSize: "10px" } },
            open ? "▾" : "▸",
          )
        : null,
      React.createElement(
        "span",
        {
          style: {
            color: col.border,
            border: "1px solid " + col.border,
            borderRadius: "3px",
            padding: "0 4px",
            fontSize: "10px",
            fontWeight: "bold",
          },
        },
        col.tag,
      ),
      React.createElement("span", { style: { color: col.label } }, label),
    ),
    open && hasChildren
      ? React.createElement(
          "div",
          {
            style: {
              marginTop: "3px",
              borderLeft: "1px dashed #3c3c3c",
              paddingLeft: "4px",
            },
          },
          node.sub
            ? React.createElement(TreeNode, {
                node: node.sub,
                depth: depth + 1,
              })
            : null,
          node.fun
            ? React.createElement(
                "div",
                null,
                React.createElement(
                  "div",
                  {
                    style: {
                      color: "#858585",
                      fontSize: "11px",
                      margin: "2px 0",
                    },
                  },
                  "├─ fun",
                ),
                React.createElement(TreeNode, {
                  node: node.fun,
                  depth: depth + 1,
                }),
                React.createElement(
                  "div",
                  {
                    style: {
                      color: "#858585",
                      fontSize: "11px",
                      margin: "2px 0",
                    },
                  },
                  "└─ arg",
                ),
                React.createElement(TreeNode, {
                  node: node.arg,
                  depth: depth + 1,
                }),
              )
            : null,
        )
      : null,
  );
}

// ── Widget principale ─────────────────────────────────────────────
export default function DeductionWidget(props) {
  // Accesso corretto all'RPC tramite context
  const rs = useRpcSession();
  const ec = useContext(EditorContext);

  const [result, setResult] = useState(null);
  const [error, setError] = useState(null);
  const [loading, setLoading] = useState(false);

  // Forza sempre una nuova chiamata RPC ignorando la cache
  useEffect(() => {
    const pos = props.pos;
    if (!pos || !rs) return;
    setError(null);
    rs.call("getDeductionAtCursor", { pos })
      .then((res) => {
        const tree = JSON.parse(res.treeJson);
        setResult({ name: res.thmName, type: res.thmType, tree });
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
  }, [props.pos, rs]);

  const containerStyle = {
    background: "#1e1e1e",
    color: "#d4d4d4",
    padding: "12px",
    fontFamily: "monospace",
    fontSize: "13px",
    minHeight: "60px",
    overflowX: "auto",
  };

  if (!rs)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#f44747" } },
      "⚠ RpcContext non disponibile",
    );

  if (loading)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: "#858585" } },
      "⟳ Caricamento albero...",
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
      "Sposta il cursore su un teorema...",
    );

  return React.createElement(
    "div",
    { style: containerStyle },
    React.createElement("p", { style: { color: "#efefef" }, result }),
    // Intestazione
    React.createElement(
      "div",
      {
        style: {
          borderBottom: "1px solid #3c3c3c",
          marginBottom: "10px",
          paddingBottom: "6px",
        },
      },
      React.createElement(
        "span",
        { style: { color: "#9cdcfe", fontWeight: "bold" } },
        result.name,
      ),
      React.createElement("span", { style: { color: "#858585" } }, " : "),
      React.createElement("span", { style: { color: "#ce9178" } }, result.type),
    ),
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
    // Albero
    React.createElement(TreeNode, { node: result.tree, depth: 0 }),
  );
}
