import * as React from "react";
const { useState, useEffect, useContext, createContext } = React;
import { useRpcSession, EditorContext } from "@leanprover/infoview";

// ──────────────────────────────────────────────────────────────────
// Style constants (invariati)
// ──────────────────────────────────────────────────────────────────
const versionInfo = `Loaded: ${new Date().toLocaleTimeString()}`;
const WHITE = "#d4d4d4";
const LIGHTER_GRAY = "#858585";
const LIGHT_GRAY = "#3c3c3c";
const DARK_GRAY = "#1e1e1e";
const ACCENT = "#f57d33";
const PRIMARY = "#42729b";
const LIGHT_PRIMARY = "#708ba3";
const ERROR_RED = "#f44747";

const containerStyle = {
  background: "#1e1e1e",
  color: "#d4d4d4",
  fontFamily: "monospace",
  fontSize: "12px",
  minHeight: "60px",
  overflowX: "auto",
  padding: "0.5rem",
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

// ──────────────────────────────────────────────────────────────────
// HypothesesContext
// ──────────────────────────────────────────────────────────────────

const HypothesesContext = createContext({
  hypotheses: [],
  setHypotheses: () => {},
});

// ──────────────────────────────────────────────────────────────────
// Natural Deduction Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

const Leaf = ({ name, formula, isDischarged }) => {
  return React.createElement(
    "div",
    {
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
        padding: "0 6px",
        color: "green",
      },
    },
    React.createElement(
      "span",
      { style: { whiteSpace: "nowrap" } },
      `${isDischarged ? "[" : ""}${name} : ${formula}${isDischarged ? "]" : ""}`,
    ),
  );
};

const Node = ({ hypotheses, formula, rule, children }) => {
  const { sharedHypotheses, setHypotheses } = useContext(HypothesesContext);
  const [selected, setSelected] = useState(false);

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) {
      setSelected(false);
    }
  }, [sharedHypotheses]);

  const handleClick = () => {
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : []);
      return newSelected;
    });
  };

  return React.createElement(
    "div",
    {
      style: {
        // inline-flex: the node shrinks to fit its content.
        // flex-direction column: width = max(children-row, conclusion).
        // The bar (width:100%) will therefore be exactly that wide — no more.
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
        padding: "0 .1rem",
      },
    },
    // ── Premesse affiancate ──
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          flexDirection: "row",
          alignItems: "flex-end",
          gap: "16px",
          paddingBottom: "2px",
        },
      },
      children.map((child, i) =>
        React.createElement(NDTree, { key: i, tree: child }),
      ),
    ),
    // ── Barra + regola ──
    // width:100% here refers to the inline-flex container's intrinsic width,
    // i.e. max(children-row, conclusion) — exactly what we want.
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          flexDirection: "row",
          alignItems: "center",
          width: "100%",
        },
      },
      React.createElement("div", {
        style: {
          flexGrow: 1,
          height: "0.1rem",
          background: WHITE,
        },
      }),
      React.createElement(
        "span",
        {
          style: {
            marginLeft: "5px",
            color: LIGHTER_GRAY,
            fontSize: "10px",
            whiteSpace: "nowrap",
            userSelect: "none",
            lineHeight: 1,
          },
        },
        rule,
      ),
    ),
    // ── Conclusione (cliccabile) ──
    React.createElement(
      "span",
      {
        style: {
          color: WHITE,
          background: selected
            ? `color-mix(in srgb, ${ACCENT}, rgba(255, 255, 255, 0.1))`
            : "transparent",
          padding: "0.05rem 0.2rem",
          cursor: "pointer",
          whiteSpace: "nowrap",
          marginTop: "0.1rem",
        },
        onClick: handleClick,
      },
      formula,
    ),
  );
};

const OpenNode = ({ hypotheses, formula }) => {
  const { sharedHypotheses, setHypotheses } = useContext(HypothesesContext);
  const [selected, setSelected] = useState(false);

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) {
      setSelected(false);
    }
  }, [sharedHypotheses]);

  const handleClick = () => {
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : []);
      return newSelected;
    });
  };

  return React.createElement(
    "div",
    {
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
        padding: "0 4px",
      },
    },
    React.createElement(
      "span",
      {
        style: {
          color: WHITE,
          background: selected ? ACCENT : "transparent",
          border: `1px dashed ${LIGHTER_GRAY}`,
          padding: "1px 4px",
          borderRadius: "3px",
          cursor: "pointer",
          whiteSpace: "nowrap",
        },
        onClick: handleClick,
      },
      formula,
    ),
  );
};

const Unhandled = (json) =>
  React.createElement("div", { style: { color: "red" } }, "unhandled");

const NDTree = ({ tree }) => {
  switch (tree.type) {
    case "leaf":
      return React.createElement(Leaf, { ...tree });
    case "node":
      return React.createElement(Node, { ...tree });
    case "openNode":
      return React.createElement(OpenNode, { ...tree });
    default:
      return React.createElement(Unhandled, tree.stringify?.() ?? "unhandled");
  }
};

// ──────────────────────────────────────────────────────────────────
// HypothesesDisplay — mostra le ipotesi affiancate
// ──────────────────────────────────────────────────────────────────

const HypothesesDisplay = () => {
  const { sharedHypotheses } = useContext(HypothesesContext);

  return React.createElement(
    "div",
    {
      style: {
        background: DARK_GRAY,
        padding: "0.5rem",
        borderRadius: "4px",
        display: "flex",
        flexDirection: "row",
        overflowX: "auto",
        alignItems: "center",
        gap: "0.5rem",
        minHeight: "36px",
      },
    },
    React.createElement(
      "span",
      { style: { color: LIGHTER_GRAY, flexShrink: 0 } },
      `Ipotesi (${sharedHypotheses.length}):`,
    ),
    sharedHypotheses.length === 0
      ? React.createElement(
          "span",
          { style: { color: LIGHTER_GRAY, fontStyle: "italic" } },
          "nessuna — clicca un nodo",
        )
      : sharedHypotheses.map((hyp, i) =>
          React.createElement(
            "span",
            {
              key: i,
              style: {
                background: LIGHT_GRAY,
                border: `1px solid ${PRIMARY}`,
                borderRadius: "3px",
                padding: "2px 6px",
                color: WHITE,
                whiteSpace: "nowrap",
              },
            },
            React.createElement(Leaf, {
              name: hyp.name,
              formula: hyp.value.formula,
              isDischarged: false,
            }),
          ),
        ),
  );
};

// ──────────────────────────────────────────────────────────────────
// Main Widget
// ──────────────────────────────────────────────────────────────────

export default function NDTreeViewer(props) {
  const rs = useRpcSession();

  const [result, setResult] = useState(null);
  const [error, setError] = useState(null);
  const [sharedHypotheses, setHypotheses] = useState([]);

  useEffect(() => {
    const pos = props.pos;
    if (!pos || !rs) return;
    setError(null);
    rs.call("getTreeAsJson", { pos })
      .then((res) => {
        const validJSON = res.treeJson.replace(/[\x00-\x1F\x7F-\x9F]/g, "");
        const tree = JSON.parse(validJSON);
        setResult({
          name: res.thmName,
          type: res.thmType,
          tree,
          treeJson: res.treeJson,
        });
        setHypotheses([]); // reset al cambio di teorema
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
    console.log("Fetching NDTree for position", pos);
  }, [props.pos, rs]);

  if (!rs)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: ERROR_RED } },
      `⚠ RpcContext non disponibile (${versionInfo})`,
    );

  if (error)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: ERROR_RED } },
      `⚠ ${error} (${versionInfo})`,
    );

  if (!result)
    return React.createElement(
      "div",
      { style: { ...containerStyle, color: LIGHTER_GRAY } },
      `Sposta il cursore su un teorema per visualizzare l'NDTree... (${versionInfo})`,
    );

  return React.createElement(
    // Outer container: flex column, all children start from left
    "div",
    {
      style: {
        ...containerStyle,
        display: "flex",
        flexDirection: "column",
        alignItems: "stretch",
        gap: "0.5rem",
        padding: "0.5rem",
      },
    },

    // ── Header: nome e tipo del teorema ──
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          alignItems: "center",
          gap: "1rem",
        },
      },
      React.createElement(
        "p",
        { style: { color: ACCENT, flexGrow: 0, margin: 0 } },
        result.name + ":",
      ),
      React.createElement(
        "p",
        { style: { color: LIGHT_PRIMARY, flexGrow: 1, margin: 0 } },
        result.type,
      ),
    ),

    // ── Context wraps both the hypothesis bar and the tree ──
    // HypothesesDisplay sits OUTSIDE the scrollable tree area,
    // but both share the same context so clicks still propagate.
    React.createElement(
      HypothesesContext.Provider,
      { value: { sharedHypotheses, setHypotheses } },

      // Hypothesis display — fixed above, never scrolls with the tree
      React.createElement(HypothesesDisplay, null),

      // Tree scroll container
      // overflow:auto + inline-block trick: the scroll container
      // grows only as wide as the tree needs, so it never pushes
      // content off the left edge.
      React.createElement(
        "div",
        {
          style: {
            overflowX: "auto",
            outline: `1px solid ${LIGHT_GRAY}`,
            padding: "0.5rem",
            // "inline-block" makes the container hug the tree width;
            // combined with overflow:auto this gives a left-anchored
            // scrollable region that does not exceed the panel width.
            display: "block",
          },
        },
        // Wrap NDTree in a div that is inline-flex so the tree node
        // starts from the left and is never stretched to full width.
        React.createElement(
          "div",
          { style: { display: "inline-flex" } },
          React.createElement(NDTree, { tree: result.tree }),
        ),
      ),
    ),
  );
}