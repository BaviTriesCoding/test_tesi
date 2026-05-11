import * as React from "react";
const { useState, useEffect, useContext, createContext, useLayoutEffect } =
  React;
import { useRpcSession, EditorContext, RpcContext } from "@leanprover/infoview";
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
  overflowX: "auto",
};

// ──────────────────────────────────────────────────────────────────
// HypothesesContext
// ──────────────────────────────────────────────────────────────────

const HypothesesContext = createContext({
  sharedHypotheses: [],
  setHypotheses: () => {},
  selectedHypTree: null,
  setSelectedHypTree: () => {},
});

const resultContext = createContext({
  result: null,
  setResult: () => {},
});

// ──────────────────────────────────────────────────────────────────
// Natural Deduction Tree Node Renderer
// ──────────────────────────────────────────────────────────────────

const Leaf = ({
  hypotheses,
  name,
  formula,
  isDischarged,
  disableClick,
  uniqueId,
}) => {
  const { sharedHypotheses, setHypotheses, setSelectedHypTree } =
    useContext(HypothesesContext);
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
      setSelectedHypTree(null);
      return newSelected;
    });
  };

  return React.createElement(
    "div",
    {
      id: uniqueId,
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
      },
    },
    React.createElement(
      "span",
      {
        className: "formula",
        style: {
          color: "green",
          background: selected
            ? `color-mix(in srgb, ${ACCENT}, rgba(255,255,255,0.1))`
            : "transparent",
          cursor: disableClick ? "default" : "pointer",
          whiteSpace: "nowrap",
          textAlign: "center",
          lineHeight: "1rem",
          padding: "0 0.5rem",
        },
        onClick: handleClick,
      },
      `${isDischarged ? "[" : ""}${name} : ${formula}${isDischarged ? "]" : ""}`,
    ),
  );
};

const Node = ({
  hypotheses,
  formula,
  rule,
  children,
  disableClick,
  uniqueId,
}) => {
  const { sharedHypotheses, setHypotheses, setSelectedHypTree } =
    useContext(HypothesesContext);
  const { result } = useContext(resultContext);

  const [selected, setSelected] = useState(false);
  const [lineInfo, setLineInfo] = useState({
    width: 0,
    marginLeft: 0,
  });

  const rs = useRpcSession();

  useEffect(() => {
    if (selected && sharedHypotheses !== hypotheses) setSelected(false);
  }, [sharedHypotheses]);

  useLayoutEffect(() => {
    const firstFormula = document
      .querySelector(`#${uniqueId}0 > .formula`)
      .getBoundingClientRect();
    const lastFormula = document
      .querySelector(`#${uniqueId}${children.length - 1} > .formula`)
      .getBoundingClientRect();
    const parentFormula = document
      .querySelector(`#${uniqueId} > .formula`)
      .getBoundingClientRect();
    const lineWidth = Math.max(
      lastFormula.right - firstFormula.left,
      parentFormula.width,
    );
    const marginLeft =
      firstFormula.left -
      (parentFormula.left + parentFormula.width / 2 - lineWidth / 2);

    setLineInfo({
      width: lineWidth,
      marginLeft:
        parentFormula.width >= lastFormula.right - firstFormula.left
          ? 0
          : 2 * marginLeft,
    });
  }, [result]);

  const handleClick = () => {
    if (disableClick) return;
    setSelected((prev) => {
      const newSelected = !prev;
      setHypotheses(newSelected ? (hypotheses ?? []) : null);
      setSelectedHypTree(null);
      return newSelected;
    });
  };

  return React.createElement(
    "div",
    {
      id: uniqueId,
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
        gap: "0.5rem",
        position: "relative",
      },
    },
    // ── Riga delle premesse ──────────────────────────────────────────
    React.createElement(
      "div",
      {
        style: {
          display: "flex",
          flexDirection: "row",
          alignItems: "flex-end",
          gap: "3rem",
        },
      },
      children.map((child, i) =>
        React.createElement(NDTree, {
          key: i,
          tree: child,
          disableClick,
          uniqueId: uniqueId + i,
        }),
      ),
    ),

    // ── Barra + etichetta regola ─────────────────────────────────────
    React.createElement(
      "div",
      {
        className: "line",
        style: {
          position: "relative",
          height: "0.125rem",
          borderRadius: "10rem",
          background: WHITE,
          width: `${lineInfo.width}px`,
          marginLeft: `${lineInfo.marginLeft}px`,
        },
      },
      React.createElement(
        "span",
        {
          style: {
            position: "absolute",
            left: "100%",
            color: LIGHTER_GRAY,
            whiteSpace: "nowrap",
            userSelect: "none",
            lineHeight: 1,
            fontSize: "0.5rem",
            marginLeft: "0.25rem",
          },
        },
        rule,
      ),
    ),

    // ── Conclusione (cliccabile) ─────────────────────────────────────
    React.createElement(
      "span",
      {
        className: "formula",
        style: {
          color: WHITE,
          background: selected
            ? `color-mix(in srgb, ${ACCENT}, rgba(255,255,255,0.1))`
            : "transparent",
          cursor: disableClick ? "default" : "pointer",
          whiteSpace: "nowrap",
          textAlign: "center",
          lineHeight: "1rem",
          padding: "0 0.5rem",
        },
        onClick: handleClick,
      },
      formula,
    ),
  );
};

const OpenNode = ({ hypotheses, formula, disableClick, uniqueId }) => {
  const { sharedHypotheses, setHypotheses, setSelectedHypTree } =
    useContext(HypothesesContext);
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
      setSelectedHypTree(null);
      return newSelected;
    });
  };

  return React.createElement(
    "div",
    {
      id: uniqueId,
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
      },
    },
    React.createElement(
      "span",
      {
        className: "formula",
        style: {
          color: WHITE,
          background: selected
            ? `color-mix(in srgb, ${ACCENT}, rgba(255,255,255,0.1))`
            : "transparent",
          cursor: disableClick ? "default" : "pointer",
          whiteSpace: "nowrap",
          textAlign: "center",
          lineHeight: "1rem",
          padding: "0 0.5rem",
          outline: "dashed 0.0625rem",
          borderRadius: "0.25rem",
        },
        onClick: handleClick,
      },
      formula,
    ),
  );
};

const Unhandled = (uniqueId) => {
  return React.createElement(
    "div",
    {
      id: uniqueId,
      style: {
        display: "inline-flex",
        flexDirection: "column",
        alignItems: "center",
      },
    },
    React.createElement(
      "span",
      {
        className: "formula",
        style: {
          color: ERROR_RED,
          whiteSpace: "nowrap",
          textAlign: "center",
          lineHeight: "1rem",
          padding: "0 0.5rem",
        },
      },
      "Unhandled",
    ),
  );
};

const NDTree = ({ tree, disableClick, uniqueId }) => {
  switch (tree?.type) {
    case "leaf":
      return React.createElement(Leaf, {
        ...tree,
        disableClick: disableClick,
        uniqueId: uniqueId,
      });
    case "node":
      return React.createElement(Node, {
        ...tree,
        disableClick: disableClick,
        uniqueId: uniqueId,
      });
    case "openNode":
      return React.createElement(OpenNode, {
        ...tree,
        disableClick: disableClick,
        uniqueId: uniqueId,
      });
    default:
      return React.createElement(Unhandled, { uniqueId: uniqueId });
  }
};

// ──────────────────────────────────────────────────────────────────
// HypothesesDisplay — mostra le ipotesi affiancate
// ──────────────────────────────────────────────────────────────────

const HypothesesDisplay = () => {
  const { sharedHypotheses, selectedHypTree, setSelectedHypTree } =
    useContext(HypothesesContext);

  const handleHypClick = (hyp, i) => {
    if (hyp.value.type === "leaf") return;
    if (selectedHypTree?.id === i) {
      // deselect
      setSelectedHypTree(null);
    } else {
      setSelectedHypTree({ id: i, value: hyp.value });
    }
  };

  return React.createElement(
    "div",
    {
      style: {
        display: "flex",
        flexDirection: "row",
        flexWrap: "wrap",
        alignItems: "center",
        gap: "0.5rem",
      },
    },
    sharedHypotheses.map((hyp, i) =>
      React.createElement(
        "span",
        {
          key: i,
          onClick: () => handleHypClick(hyp, i),
          style: {
            border: `0.0125rem solid ${selectedHypTree?.id === i ? PRIMARY : LIGHT_GRAY}`,
            borderRadius: "0.125rem",
            color: WHITE,
            cursor: hyp.value.type !== "leaf" ? "pointer" : "default",
            userSelect: "none",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            whiteSpace: "nowrap",
            textAlign: "center",
            lineHeight: "1rem",
            padding: "0.25rem 0.5rem",
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
  const [selectedHypTree, setSelectedHypTree] = useState(null);

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
        setSelectedHypTree(null);
      })
      .catch((e) => setError(e.message ?? "Errore RPC sconosciuto"));
  }, [props.pos, rs]);

  useEffect(() => {
    setSelectedHypTree(null);
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
        fontFamily: "monospace",
        display: "flex",
        flexDirection: "column",
        alignItems: "stretch",
        gap: "0.5rem",
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
        {
          style: { color: ACCENT, flexGrow: 0, margin: 0 },
        },
        result.name + ":",
      ),
      React.createElement(
        "p",
        {
          style: { color: LIGHT_PRIMARY, flexGrow: 1, margin: 0 },
        },
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
          selectedHypTree,
          setSelectedHypTree,
        },
      },
      React.createElement(
        resultContext.Provider,
        {
          value: {
            result,
            setResult,
          },
        },

        selectedHypTree &&
          React.createElement(
            "div",
            {
              style: {
                overflowX: "auto",
                outline: `0.0625 solid ${LIGHT_GRAY}`,
                display: "flex",
                padding: "1rem",
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
                tree: selectedHypTree?.value,
                disableClick: true,
                uniqueId: "hypNode",
              }),
            ),
          ),

        // Hypothesis display — fixed above, never scrolls with the tree
        sharedHypotheses?.length > 0 &&
          React.createElement(HypothesesDisplay, null),

        React.createElement(
          "div",
          {
            style: {
              overflowX: "auto",
              outline: `0.0625rem solid ${LIGHT_GRAY}`,
              display: "flex",
              padding: "1rem",
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
              uniqueId: "node",
            }),
          ),
        ),
      ),
    ),
  );
}
