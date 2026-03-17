import Lean
open Lean Meta Server Widget

-- ══════════════════════════════════════════════════════════════════
-- TIPO DeductionTree
-- ══════════════════════════════════════════════════════════════════

inductive DeductionTree where
  | hyp     : Name → Expr → DeductionTree
  | axiom_  : Name → Expr → DeductionTree
  | lam     : Name → Expr → DeductionTree → DeductionTree
  | app     : DeductionTree → DeductionTree → Expr → DeductionTree
  | forall_ : Name → Expr → DeductionTree → DeductionTree
  | other   : Expr → Expr → DeductionTree
  deriving Repr

-- ══════════════════════════════════════════════════════════════════
-- COSTANTI OPACHE (sorry, ecc.)
-- ══════════════════════════════════════════════════════════════════

def opaqueConsts : List Name :=
  [``sorryAx, ``Classical.choice, ``Quot.lift, ``Quot.mk]

def isOpaqueOrSorry (e : Expr) : Bool :=
  match e.getAppFn with
  | .const name _ => opaqueConsts.contains name
  | _             => false

-- ══════════════════════════════════════════════════════════════════
-- COSTRUZIONE DELL'ALBERO
-- ══════════════════════════════════════════════════════════════════

partial def exprToDeductionTree (e : Expr) (fuel : Nat := 100) : MetaM DeductionTree := do
  if fuel == 0 then
    let ty ← inferType e
    return .other e ty
  if isOpaqueOrSorry e then
    let ty ← inferType e
    return .other e ty
  let e ← whnf e
  if isOpaqueOrSorry e then
    let ty ← inferType e
    return .other e ty
  match e with
  | .fvar fvarId =>
    let decl ← fvarId.getDecl
    return .hyp decl.userName decl.type
  | .const name _ =>
    if opaqueConsts.contains name then
      let ty ← inferType e
      return .other e ty
    let ty ← inferType e
    return .axiom_ name ty
  | .lam binderName binderType body _bi =>
    withLocalDecl binderName .default binderType fun fvar => do
      let body' := body.instantiate1 fvar
      let sub ← exprToDeductionTree body' (fuel - 1)
      return .lam binderName binderType sub
  | .app f a =>
    let ty ← inferType e
    let tF ← exprToDeductionTree f (fuel - 1)
    let tA ← exprToDeductionTree a (fuel - 1)
    return .app tF tA ty
  | .forallE binderName binderType body _bi =>
    withLocalDecl binderName .default binderType fun fvar => do
      let body' := body.instantiate1 fvar
      let sub ← exprToDeductionTree body' (fuel - 1)
      return .forall_ binderName binderType sub
  | _ =>
    let ty ← inferType e
    return .other e ty

-- ══════════════════════════════════════════════════════════════════
-- SERIALIZZAZIONE JSON DELL'ALBERO
-- ══════════════════════════════════════════════════════════════════

/-- Serializza il DeductionTree come Json -/
partial def DeductionTree.toJson (tree : DeductionTree) : MetaM String := do
  match tree with
  | .hyp name ty =>
    let tyStr ← ppExpr ty
    return "{\"kind\":\"hyp\",\"name\":\"" ++ escapeJson (toString name) ++ "\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\"}"
  | .axiom_ name ty =>
    let tyStr ← ppExpr ty
    return "{\"kind\":\"axiom\",\"name\":\"" ++ escapeJson (toString name) ++ "\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\"}"
  | .lam name ty sub =>
    let tyStr ← ppExpr ty
    let subJson ← sub.toJson
    return "{\"kind\":\"lam\",\"name\":\"" ++ escapeJson (toString name) ++ "\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\",\"sub\":" ++ subJson ++ "}"
  | .forall_ name ty sub =>
    let tyStr ← ppExpr ty
    let subJson ← sub.toJson
    return "{\"kind\":\"forall\",\"name\":\"" ++ escapeJson (toString name) ++ "\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\",\"sub\":" ++ subJson ++ "}"
  | .app tF tA resTy =>
    let tyStr ← ppExpr resTy
    let jsonF ← tF.toJson
    let jsonA ← tA.toJson
    return "{\"kind\":\"app\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\",\"fun\":" ++ jsonF ++ ",\"arg\":" ++ jsonA ++ "}"
  | .other _ ty =>
    let tyStr ← ppExpr ty
    return "{\"kind\":\"sorry\",\"type\":\"" ++ escapeJson (toString tyStr) ++ "\"}"
where
  escapeJson (s : String) : String :=
    s.foldl (fun acc c =>
      match c with
      | '"'  => acc ++ "\\\""
      | '\\' => acc ++ "\\\\"
      | '\n' => acc ++ "\\n"
      | '\r' => acc ++ "\\r"
      | '\t' => acc ++ "\\t"
      | c    => acc ++ String.singleton c) ""

-- ══════════════════════════════════════════════════════════════════
-- RPC PARAMS & RESULT
-- ══════════════════════════════════════════════════════════════════

structure DeductionAtCursorParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure DeductionAtCursorResult where
  thmName  : String
  thmType  : String
  treeJson : String
  deriving FromJson, ToJson, Server.RpcEncodable

-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD
-- ══════════════════════════════════════════════════════════════════

open RequestM in
@[server_rpc_method]
def getDeductionAtCursor (params : DeductionAtCursorParams) :
    RequestM (RequestTask DeductionAtCursorResult) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
    let doc ← readDoc
    let txt := doc.meta.text  -- FileMap per convertire posizioni
    let pos := txt.lspPosToUtf8Pos params.pos
    let l := Elab.InfoTree.goalsAt? txt snap.infoTree pos
    let [item] := l | throwError "alsfdslfs"
    let .some name := item.ctxInfo.parentDecl? | throwError "u uu"
    let info ← try getConstInfo name
      catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
      let tyStr ← ppExpr info.type
      match info.value? with
      | none =>
        return { thmName := toString name, thmType := toString tyStr,
                  treeJson := "{\"kind\":\"sorry\",\"type\":\"axiom - no proof term\"}" }
      | some proofTerm =>
        let tree     ← exprToDeductionTree proofTerm
        let treeJson ← tree.toJson
        return { thmName := toString name, thmType := toString tyStr, treeJson := treeJson }

-- ══════════════════════════════════════════════════════════════════
-- WIDGET JAVASCRIPT
-- ══════════════════════════════════════════════════════════════════
@[widget_module]
def DeductionTreeWidget : Widget.Module where
  javascript := include_str "DeductionTreeWidget.js"

-- ══════════════════════════════════════════════════════════════════
-- ATTIVA IL WIDGET
-- ══════════════════════════════════════════════════════════════════
show_panel_widgets [DeductionTreeWidget]

theorem modus_ponens (P Q : Prop) (h1 : P → Q) (h2 : P) : Q :=
  h1 h2

theorem modus_ponens1 (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  apply h2

theorem imp_trans (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  apply fun h => g (f h)

theorem AandBThenA (P Q K : Prop) (h1: P ∧ Q) (h2: P → K) : K := by
  apply h2 (h1.left)

-- Per disattivare il widget in una sezione:
show_panel_widgets [- DeductionTreeWidget]
