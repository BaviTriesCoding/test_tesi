import Lean
open Lean Meta Server Widget

-- ══════════════════════════════════════════════════════════════════
-- Natural Deduction Tree Type
-- ══════════════════════════════════════════════════════════════════

abbrev Formula := String -- Quello che c'è scritto nelle foglie
abbrev ProofMethod := String -- ¬i, ∧e1, ∧e2, ∧i, ∨i1, ∨i2, ∨e, →i, →e, etc.
abbrev isOpen := Bool --Il booleano è per capire se è una foglia aperta o scaricata

inductive NDTree where
  | leaf      : Formula → isOpen → NDTree
  | node      : List NDTree → Formula → ProofMethod → NDTree -- La stringa è per il nome del teorema o della regola usata
  | unhandled : Formula → NDTree                        -- Per rappresentare i nodi che non siamo ancora in grado di gestire
  deriving FromJson, ToJson, Server.RpcEncodable

def NDTree.toString : NDTree → String
  | .leaf f isOpen => s!"{if isOpen then "Open" else "Closed"} leaf: {f}"
  | .node children f rule => s!"Node: {f} (rule: {rule})\n" ++ "\n".intercalate (children.map (toString ·))
  | .unhandled f => s!"Unhandled node: {f}"


-- ══════════════════════════════════════════════════════════════════
-- RPC PARAMS & RESULT
-- ══════════════════════════════════════════════════════════════════

structure DeductionAtCursorParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure DeductionAtCursorResult where
  thmName  : String
  thmType  : String
  deriving FromJson, ToJson, Server.RpcEncodable

structure TreeAsJsonResult where
  thmName : String
  thmType : String
  treeJson : String
  deriving FromJson, ToJson, Server.RpcEncodable

-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD
-- ══════════════════════════════════════════════════════════════════

#check ConstantInfo
#check Elab.GoalsAtResult
#check Elab.ContextInfo

partial def exprInfo (e : Expr) : MetaM String := do
  match e with
  | .bvar idx         => return s!".bvar {idx}"
  | .fvar _ =>
      let decl ← Meta.getFVarLocalDecl e
      return s!".fvar {decl.userName}"
  | .mvar id          => return s!".mvar {id.name}"
  | .sort lvl         => return s!".sort {lvl}"
  | .const name us    => return s!".const {name} {us}"
  | .app fn arg       =>
      return s!".app ({← exprInfo fn}) ({← exprInfo arg})"
  | .lam n t b bi =>
    let tStr ← exprInfo t
    let displayName := if isHygienicName n then "✝" else n.toString
    Meta.withLocalDecl n bi t fun fv => do
      let bStr ← exprInfo (b.instantiate1 fv)
      return s!".lam {displayName} : ({tStr}) => ({bStr})"
  | .forallE n t b bi =>
    if e.isArrow then
      -- non dipendente: ignora il nome del binder
      return s!"({← exprInfo t}) → ({← exprInfo b})"
    else
      let tStr ← exprInfo t
      Meta.withLocalDecl n bi t fun fv => do
        let bStr ← exprInfo (b.instantiate1 fv)
        return s!"∀ {n} : ({tStr}), ({bStr})"
  | .letE n t v b _   =>
      let tStr ← exprInfo t
      let vStr ← exprInfo v
      let bStr ← exprInfo b
      return s!".let {n} : ({tStr}) := ({vStr}); {bStr}"
  | .lit (.natVal n)  => return s!"Nat {n}"
  | .lit (.strVal s)  => return s!"Str {s}"
  | .mdata _ e        => exprInfo e
  | .proj tn idx s    =>
      return s!".proj {tn}.{idx} ({← exprInfo s})"
  where
    isHygienicName (n : Name) : Bool := n.toString.contains "_@" || n.toString.contains "_hyg"

#check Name
#check Lean.Expr.getAppFnArgs


-- Versione monadica che usa exprInfo
partial def Lean.Expr.toNDTreeM (e : Expr) : MetaM NDTree := do
  match e with
  -- per le app, creo un nodo con i figli che sono gli argomenti, e come formula la stringa del tipo dell'applicazione
  | .app _ _ => do
      let (fn, args) := e.getAppFnArgs
      let mut argList : List NDTree := []
      for arg in args do
        let subtree ← arg.toNDTreeM
        argList := argList ++ [subtree]
      return .node argList s!"{← exprInfo e}" fn.toString

  | .lam _ _ body _ => do
      return .node [← body.toNDTreeM] s!"{← exprInfo e}" "λ"
  | .forallE _ _ body _ => do
      let subtree ← body.toNDTreeM
      return subtree
  | .letE _ _ _ body _ => do
      let subtree ← body.toNDTreeM
      return subtree
  | .mdata _ e => do
      let subtree ← e.toNDTreeM
      return subtree
  | .proj _ _ e => do
      let subtree ← e.toNDTreeM
      return subtree

  -- tutti i nodi finali li stampiamo come leaf, con la formula che è la stringa del tipo
  | e => return .leaf (← exprInfo e) false



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
    dbg_trace s!"Found declaration: {name}"
    let info ← try getConstInfo name
      catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
      dbg_trace s!"info.name: {info.name},\n
        info.type: {← ppExpr info.type},\n
        info.value: {info.value?},\n
        info.levelParams: {info.levelParams},\n
        info.all: {info.all}" -- debug, per vedere cosa c'è dentro info
      let tyStr ← ppExpr info.type
      match info.value? with
      | none =>
        return { thmName := toString name, thmType := toString tyStr}
      | some proofTerm =>
        let tree ← proofTerm.toNDTreeM
        dbg_trace s!"Found proof term for {name}: {tree.toString}"
        return { thmName := toString name, thmType := toString tyStr }

-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD: GET TREE AS JSON
-- ══════════════════════════════════════════════════════════════════

open RequestM in
@[server_rpc_method]
def getTreeAsJson (params : DeductionAtCursorParams) :
    RequestM (RequestTask TreeAsJsonResult) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
    let doc ← readDoc
    let txt := doc.meta.text
    let pos := txt.lspPosToUtf8Pos params.pos
    let l := Elab.InfoTree.goalsAt? txt snap.infoTree pos
    let [item] := l | throwError "Impossibile trovare il nodo a questa posizione"
    let .some name := item.ctxInfo.parentDecl? | throwError "Impossibile trovare la dichiarazione"
    let info ← try getConstInfo name
      catch _ => throwThe RequestError ⟨.invalidParams, s!"Costante '{name}' non trovata"⟩
    let tyStr ← ppExpr info.type
    match info.value? with
    | none =>
      let emptyTree := NDTree.unhandled ""
      return { thmName := toString name, thmType := toString tyStr, treeJson := s!"{toJson emptyTree}" }
    | some proofTerm =>
      let tree ← proofTerm.toNDTreeM
      dbg_trace s!"Found proof term for {name}: {← exprInfo proofTerm}"
      return { thmName := toString name, thmType := toString tyStr, treeJson := s!"{toJson tree}" }

-- ══════════════════════════════════════════════════════════════════
-- WIDGET JAVASCRIPT
-- ══════════════════════════════════════════════════════════════════
@[widget_module]
def DeductionTreeWidget : Widget.Module where
  javascript := include_str "newTry.js"

@[widget_module]
def NDTreeJsonViewerWidget : Widget.Module where
  javascript := include_str "NDTreeJsonViewer.js"

-- ══════════════════════════════════════════════════════════════════
-- ATTIVA I WIDGET
-- ══════════════════════════════════════════════════════════════════
show_panel_widgets [NDTreeJsonViewerWidget]


theorem foo2 (A : Prop) (h : A) : A := by
  exact h

theorem Andleft (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | intro p _ => exact p

theorem Andright (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h with
  | intro _ q => exact q

theorem AndIntro {P Q} (h1 : P) (h2 : Q) : P ∧ Q := by
  exact And.intro h1 h2


theorem OrIntroLeft (h : P) : P ∨ Q := by
  apply Or.inl h

theorem OrIntroRight (P Q : Prop) (h : Q) : P ∨ Q := by
  apply Or.inr h

theorem OrElim (P Q R : Prop) (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := by
  cases h1 with
  | inl p => apply h2 p
  | inr q => apply h3 q

theorem NotIntro (P : Prop) (h : P → False) : ¬P := by
  apply Not.intro h

theorem NotElim (P : Prop) (h1 : ¬P) (h2 : P) : False := by
  apply h1 h2

theorem foo (A B C D : Prop) (h1: (A ∧ B) ∧ (C ∧ D)) : A ∧ C := by
  have h2 : A ∧ B := And.left h1
  have h3 : C ∧ D := And.right h1
  have a : A := And.left h2
  have c : C := And.left h3
  exact And.intro a c

theorem andAnd (A B C : Prop) (h : A ∧ (B ∧ C)) : C := by
  have h1 : B ∧ C := And.right h
  have c : C := And.right h1
  exact c

-- Per disattivare il widget in una sezione:
show_panel_widgets [- NDTreeJsonViewerWidget]
