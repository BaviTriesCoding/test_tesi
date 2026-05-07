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
  sharedHypotheses: [],
  setHypotheses: () => {},
  selectedTree: null,
  setSelectedTree: () => {},
  selectedHypIdx: null,
  setSelectedHypIdx: () => {},
});

// ──────────────────────────────────────────────────────────────────
// Natural Deduction Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

const Leaf = ({ hypotheses, name, formula, isDischarged, disableClick }) => {
  const {
    sharedHypotheses,
    setHypotheses,
    setSelectedTree,
    setSelectedHypIdx,
  } = useContext(HypothesesContext);
  const [selected, setSelected] = useState(false);

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) {
      setSelected(false);
    }
  }, [sharedHypotheses]);

  const handleClick = () => {
    if (disableClick) return;
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : null);
      setSelectedHypIdx(null);
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
          color: "green",
          background: selected ? ACCENT : "transparent",
          padding: "1px 4px",
          borderRadius: "3px",
          cursor: disableClick ? "default" : "pointer",
          whiteSpace: "nowrap",
        },
        onClick: handleClick,
      },
      `${isDischarged ? "[" : ""}${name} : ${formula}${isDischarged ? "]" : ""}`,
    ),
  );
};

const Node = ({ hypotheses, formula, rule, children, disableClick }) => {
  const {
    sharedHypotheses,
    setHypotheses,
    setSelectedTree,
    setSelectedHypIdx,
  } = useContext(HypothesesContext);
  const [selected, setSelected] = useState(false);

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) {
      setSelected(false);
    }
  }, [sharedHypotheses]);

  const handleClick = () => {
    if (disableClick) return;
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : null);
      setSelectedHypIdx(null);
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
        React.createElement(NDTree, {
          key: i,
          tree: child,
          disableClick: disableClick,
        }),
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
          cursor: disableClick ? "default" : "pointer",
          whiteSpace: "nowrap",
          marginTop: "0.1rem",
        },
        onClick: handleClick,
      },
      formula,
    ),
  );
};

const OpenNode = ({ hypotheses, formula, disableClick }) => {
  const {
    sharedHypotheses,
    setHypotheses,
    setSelectedTree,
    setSelectedHypIdx,
  } = useContext(HypothesesContext);
  const [selected, setSelected] = useState(false);

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) {
      setSelected(false);
    }
  }, [sharedHypotheses]);

  const handleClick = () => {
    if (disableClick) return;
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : null);
      setSelectedHypIdx(null);
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
          cursor: disableClick ? "default" : "pointer",
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

const NDTree = ({ tree, disableClick }) => {
  switch (tree?.type) {
    case "leaf":
      return React.createElement(Leaf, { ...tree, disableClick: disableClick });
    case "node":
      return React.createElement(Node, { ...tree, disableClick: disableClick });
    case "openNode":
      return React.createElement(OpenNode, {
        ...tree,
        disableClick: disableClick,
      });
    default:
      return React.createElement(Unhandled, tree?.stringify() ?? "unhandled");
  }
};

// ──────────────────────────────────────────────────────────────────
// SelectedTreeViewer
// ──────────────────────────────────────────────────────────────────

const SelectedTreeViewer = () => {
  const { selectedTree } = useContext(HypothesesContext);

  if (!selectedTree) return null;

  return React.createElement(
    "div",
    {
      style: {
        display: "flex",
        flexDirection: "column",
        gap: "0.25rem",
      },
    },
    // header
    React.createElement(
      "span",
      {
        style: {
          color: LIGHTER_GRAY,
          fontSize: "10px",
          userSelect: "none",
          letterSpacing: "0.05em",
          textTransform: "uppercase",
        },
      },
      "albero dell'ipotesi",
    ),
    // scrollable tree
    React.createElement(
      "div",
      {
        style: {
          overflowX: "auto",
          outline: `1px solid ${PRIMARY}`,
          padding: "0.5rem",
          display: "block",
          borderRadius: "2px",
        },
      },
      React.createElement(
        "div",
        { style: { display: "inline-flex" } },
        React.createElement(NDTree, { tree: selectedTree }),
      ),
    ),
  );
};

// ──────────────────────────────────────────────────────────────────
// HypothesesDisplay — mostra le ipotesi affiancate
// ──────────────────────────────────────────────────────────────────

const HypothesesDisplay = () => {
  const {
    sharedHypotheses,
    selectedHypIdx,
    setSelectedHypIdx,
    setSelectedTree,
  } = useContext(HypothesesContext);

  const handleHypClick = (hyp, i) => {
    if (hyp.value.type === "leaf") return;
    if (selectedHypIdx === i) {
      // deselect
      setSelectedHypIdx(null);
      setSelectedTree(null);
    } else {
      setSelectedHypIdx(i);
      setSelectedTree(hyp.value);
    }
  };

  return React.createElement(
    "div",
    {
      style: {
        background: DARK_GRAY,
        padding: "0.5rem",
        borderRadius: "4px",
        display: "flex",
        flexDirection: "row",
        flexWrap: "wrap",
        alignItems: "center",
        gap: "0.5rem",
        minHeight: "36px",
      },
    },
    sharedHypotheses.map((hyp, i) =>
      React.createElement(
        "span",
        {
          key: i,
          onClick: () => handleHypClick(hyp, i),
          style: {
            background: selectedHypIdx === i ? PRIMARY : LIGHT_GRAY,
            border: `1px solid ${selectedHypIdx === i ? LIGHT_PRIMARY : PRIMARY}`,
            borderRadius: "3px",
            padding: "0.1rem 0.5rem",
            color: WHITE,
            whiteSpace: "nowrap",
            cursor: hyp.value.type !== "leaf" ? "pointer" : "default",
            userSelect: "none",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
          },
        },
        React.createElement(
          "span",
          {
            style: {
              color: hyp.value.type === "leaf" ? "green" : WHITE,
            },
          },
          `${hyp.value?.isDischarged ? "[" : ""}${hyp.name} : ${hyp.value.formula}${hyp.value?.isDischarged ? "]" : ""}`,
        ),
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
  const [sharedHypotheses, setHypotheses] = useState(null);
  const [selectedTree, setSelectedTree] = useState(null);
  const [selectedHypIdx, setSelectedHypIdx] = useState(null);

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
        setHypotheses(null); // reset al cambio di teorema
        setSelectedTree(null);
        setSelectedHypIdx(null);
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
  }, [props.pos, rs]);

  useEffect(() => {
    setSelectedTree(null);
    setSelectedHypIdx(null);
  }, [sharedHypotheses]);

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
          flexDirection: "column",
          alignItems: "start",
          gap: "0.5rem",
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
      {
        value: {
          sharedHypotheses,
          setHypotheses,
          selectedTree,
          setSelectedTree,
          selectedHypIdx,
          setSelectedHypIdx,
        },
      },

      selectedTree &&
        React.createElement(
          "div",
          {
            style: {
              overflowX: "auto",
              outline: `1px solid ${LIGHT_GRAY}`,
              padding: "0.5rem",
              display: "flex",
            },
          },
          React.createElement(
            "div",
            {
              style: {
                display: "flex",
                alignItems: "flex-start",
                justifyContent: "center",
                margin: "0 auto",
              },
            },
            React.createElement(NDTree, {
              tree: selectedTree,
              disableClick: true,
            }),
          ),
        ),

      // Hypothesis display — fixed above, never scrolls with the tree
      sharedHypotheses && React.createElement(HypothesesDisplay, null),

      React.createElement(
        "div",
        {
          style: {
            overflowX: "auto",
            outline: `1px solid ${LIGHT_GRAY}`,
            padding: "0.5rem",
            display: "flex",
          },
        },
        React.createElement(
          "div",
          {
            style: {
              display: "flex",
              alignItems: "flex-start",
              justifyContent: "center",
              margin: "0 auto",
            },
          },
          React.createElement(NDTree, {
            tree: result.tree,
            disableClick: false,
          }),
        ),
      ),
    ),
  );
}
