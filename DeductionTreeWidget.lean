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
    withLocalDecl n bi t fun fv => do
      let bStr ← exprInfo (b.instantiate1 fv)
      return s!".lam {displayName} : ({tStr}) => ({bStr})"
  | .forallE n t b bi =>
    if e.isArrow then
      -- non dipendente: ignora il nome del binder
      return s!"({← exprInfo t}) → ({← exprInfo b})"
    else
      let tStr ← exprInfo t
      withLocalDecl n bi t fun fv => do
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


-- ══════════════════════════════════════════════════════════════════
-- MAPPING NOMI REGOLE ND
-- ══════════════════════════════════════════════════════════════════

def ruleNameOf (fn : Name) : String :=
  match fn with
  | ``And.intro    => "∧I"
  | ``And.left     => "∧E₁"
  | ``And.right    => "∧E₂"
  | ``Or.inl       => "∨I₁"
  | ``Or.inr       => "∨I₂"
  | ``Or.elim      => "∨E"
  | ``Not.intro    => "¬I"
  | ``absurd       => "¬E"
  | ``False.elim   => "⊥E"
  | ``Exists.intro => "∃I"
  | ``Exists.elim  => "∃E"
  | other          => other.toString

-- Per le app: se fn è una costante nota, usa il mapping.
-- Altrimenti, controlla il tipo di fn per capire se è →E o ∀E.
def ruleNameOfApp (e : Expr) : MetaM String := do
  match e with
  | .const name _ => return ruleNameOf name
  | _ =>
    let fnType ← inferType e
    match fnType with
    | .forallE _ _ _ _ =>
      if fnType.isArrow then return "→E"   -- P → Q applicata a P
      else return "∀E"                     -- ∀ x, P x applicata a x
    | _ => return s!"{← ppExpr e}"

-- Versione monadica che usa exprInfo
partial def Lean.Expr.toNDTreeM (e : Expr) : MetaM NDTree := do
  match e with
  | .app _ _ => do
      let (fn, args) := e.getAppFnArgs
      if fn == ``sorryAx then
        let resultType ← inferType e
        return .node [] s!"{← ppExpr resultType}" "sorry"
      let mut argList : List NDTree := []
      for arg in args do
        let argType ← inferType arg
        if !argType.isSort then
          argList := argList ++ [← arg.toNDTreeM]
      let resultType ← inferType e
      return .node argList s!"{← ppExpr resultType}" s!"{← ruleNameOfApp e}"

  -- →I se il binder è una Prop (scarica un'assunzione)
  -- ∀I se il binder è un Type (introduce una variabile)
  | .lam n t b bi => withLocalDecl n bi t fun fv => do
      let tKind ← inferType t
      let child ← (b.instantiate1 fv).toNDTreeM
      let lamType ← inferType e
      let ruleName := if tKind.isProp then "→I" else "∀I"
      return .node [child] s!"{← ppExpr lamType}" ruleName

  | .forallE n t b bi =>
      let displayName := if isHygienicName n then "✝" else n.toString
      let tStr ← ppExpr t
      if e.isArrow then
        return .node [← b.toNDTreeM] s!"{displayName} : {tStr}" "∀"
      else
        withLocalDecl n bi t fun fv => do
          return .node [← (b.instantiate1 fv).toNDTreeM] s!"∀{displayName}: {tStr}" "∀"

  | .letE _ _ _ body _ => body.toNDTreeM
  | .mdata _ e          => e.toNDTreeM
  | .proj _ _ e         => e.toNDTreeM
  | .fvar id => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      return .leaf (toString (← ppExpr decl.type)) false
  | e => return .leaf s!"{← ppExpr (← inferType e)}" false
  where
    isHygienicName (n : Name) : Bool :=
      n.toString.contains "_@" || n.toString.contains "_hyg"

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

axiom P : Prop
axiom Q : Prop
theorem AndIntro (h1 : P) (h2 : Q) : P ∧ Q := by
  exact And.intro h1 h2
#print AndIntro

theorem OrIntroLeft (P Q : Prop) (h : P) : P ∨ Q := by
  apply Or.inl h

theorem OrIntroRight (P Q: Prop) (h : Q)  : P ∨ Q := by
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
