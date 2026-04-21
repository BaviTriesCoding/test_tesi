import Lean
open Lean Meta Server Widget

-- ══════════════════════════════════════════════════════════════════
-- Natural Deduction Tree Type
-- ══════════════════════════════════════════════════════════════════

abbrev Formula := String -- Quello che c'è scritto nelle foglie
abbrev ProofMethod := String -- ¬i, ∧e1, ∧e2, ∧i, ∨i1, ∨i2, ∨e, →i, →e, etc.
abbrev isOpen := Bool --Il booleano è per capire se è una foglia aperta o scaricata
abbrev Proof := String -- Nei nodi unhandled è la prova non riconosciuta

inductive NDTree where
  | leaf      : Formula → isOpen → NDTree
  | node      : List NDTree → Formula → ProofMethod → NDTree -- La stringa è per il nome del teorema o della regola usata
  | unhandled : Proof → Formula → NDTree                        -- Per rappresentare i nodi che non siamo ancora in grado di gestire
  deriving FromJson, ToJson, Server.RpcEncodable

def NDTree.toString : NDTree → String
  | .leaf f isOpen => s!"{if isOpen then "Open" else "Closed"} leaf: {f}"
  | .node children f rule => s!"Node: {f} (rule: {rule})\n" ++ "\n".intercalate (children.map (toString ·))
  | .unhandled p f => s!"Unhandled node ({p}): {f}"

def NDTree.toJson : NDTree → String
  | .leaf f isOpen => "{\"formula\":\""++ f ++"\", \"isOpen\":\"" ++ s!"{if isOpen then "true" else "false"}" ++ "\"}"
  | .node children f rule =>
      let childrenJson := children.map toJson
      "{\"formula\":\"" ++ f ++ "\", \"rule\": \"" ++ rule ++ "\", \"premises\": [" ++ String.intercalate ", " childrenJson ++ "]}"
  | .unhandled p f => "{\"formula\":\"" ++ f ++ "\", \"unhandledProof\": \"" ++ p ++ "\"}"


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

-- For debugging: it prints the low level details of the term (e.g. bvar vs fvar)
partial def exprInfo (e : Expr) : MetaM String := do
  match /-← instantiateMVars-/ e with
  | .bvar idx         => return s!".bvar {idx}"
  | .fvar _ =>
      match (← getLCtx).find? e.fvarId! with
      | some decl =>
         return s!".fvar {decl.userName}"
      | none =>
         return s!".far UNBOUND"
  | .mvar id          => return s!".mvar {id.name}"
  | .sort lvl         => return s!".sort {lvl}"
  | .const name us    => return s!".const {name} {us}"
  | .app fn arg       =>
      return s!".app ({← exprInfo fn}) ({← exprInfo arg})"
  | .lam n t b _ =>
    let tStr ← exprInfo t
    let displayName := if isHygienicName n then "✝" else n.toString
    let bStr ← exprInfo b
    return s!".lam {displayName} : ({tStr}) => ({bStr})"
  | .forallE n t b _ =>
    if e.isArrow then
      -- non dipendente: ignora il nome del binder
      return s!"({← exprInfo t}) → ({← exprInfo b})"
    else
      let tStr ← exprInfo t
      let bStr ← exprInfo b
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
  | ``And.casesOn  => "∧E"
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
  match ← instantiateMVars e with
  | .const name _ => return ruleNameOf name
  | _ =>
    let fnType ← inferType e
    match fnType with
    | .forallE _ _ _ _ =>
      if fnType.isArrow then return "→E"   -- P → Q applicata a P
      else return "∀E"                     -- ∀ x, P x applicata a x
    | _ => return s!"{← ppExpr e}"

partial def aggressiveInstantiateMVars (e: Expr) : MetaM Expr := do
 let e ← instantiateMVars e
 match e with
 | .app _ _ => do
    match e.withApp fun e a => (e, a) with
    | (.mvar mid, args) =>
       match (← getMCtx).dAssignment.find? mid with
       | some i =>
          if i.fvars.size == args.size then
           aggressiveInstantiateMVars (.mvar i.mvarIdPending)
          else
           return e
       | none => return e
    | _ => e.traverseChildren aggressiveInstantiateMVars
 | _ => e.traverseChildren aggressiveInstantiateMVars


-- Versione monadica che usa exprInfo
partial def Lean.Expr.toNDTreeM (e' : Expr) : MetaM NDTree := do
  dbg_trace s!"Processing: {← exprInfo e'}"
  dbg_trace s!"typed as {← ppExpr (← inferType e')}"
  let e ← aggressiveInstantiateMVars e'
  dbg_trace s!"Becomes: {← exprInfo e}"
  dbg_trace s!"typed as {← ppExpr (← inferType e')}"
  dbg_trace s!"Env: {← ppExpr (Expr.bvar 0)} {← ppExpr (Expr.bvar 1)} {← ppExpr (Expr.bvar 2)}"
  dbg_trace s!"-----------------------------------"
  match e with
  | .app _ _ => do
      let (fn, args) := e.withApp fun e a => (e, a)
      if fn == const ``sorryAx [] then
        let resultType ← inferType e
        return .node [] s!"{← ppExpr resultType}" "sorry"
      let mut argList : List NDTree := []
      for arg in args do
        let argType ← inferType arg
        if !argType.isSort then
          argList := argList ++ [← arg.toNDTreeM]
      let resultType ← inferType e'
      return .node argList s!"{← ppExpr resultType}" s!"{← ruleNameOfApp fn}"

  -- →I se il binder è una Prop (scarica un'assunzione)
  -- ∀I se il binder è un Type (introduce una variabile)
  | .lam n t b bi =>
      let lamType ← ppExpr (← inferType e')  -- CSC: devi farlo PRIMA di withLocalDecl per non catturare la var
      let tKind ← inferType t
      let ruleName := if tKind.isProp then "→I" else "∀I"
      withLocalDecl n bi t fun fv => do
       let child ← (b.instantiate1 fv).toNDTreeM
       return .node [child] s!"{lamType}" ruleName

  /-  XXX TODO codice bacato
    | .forallE n t b bi =>
      let displayName := if isHygienicName n then "✝" else n.toString
      let tStr ← ppExpr t
      if e.isArrow then
        return .node [← b.toNDTreeM] s!"{displayName} : {tStr}" "∀"
      else
        withLocalDecl n bi t fun fv => do
          return .node [← (b.instantiate1 fv).toNDTreeM] s!"∀{displayName}: {tStr}" "∀"

  | .letE _ _ _ body _ => body.toNDTreeM
  | .proj _ _ e         => e.toNDTreeM -/
  | .mdata _ e          => e.toNDTreeM
  | .fvar id => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      return .leaf (toString (← ppExpr decl.type)) false
  | .mvar _ => return .leaf s!"{← ppExpr (← inferType e)}" true
  | e => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"
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
    let metavarctx := item.tacticInfo.mctxAfter
    withMCtx metavarctx do
     let younger : Name -> Name -> Bool
      | .num _ 0, .num _ _ => false
      | .num _ n, .num _ m => n < m
      | _, _ => false
     let mmmid :=
      metavarctx.eAssignment.foldl (fun m d _ => if younger m.name d.name then m else d) (MVarId.mk (.num (.anonymous) 0))
     let proofTerm := Expr.mvar mmmid
     metavarctx.decls.forM (fun id i => id.withContext do dbg_trace s!"{id.name} : {← exprInfo i.type}")
     metavarctx.eAssignment.forM (fun id e => id.withContext do dbg_trace s!"{id.name} e↦ {← exprInfo e}")
     metavarctx.dAssignment.forM (fun id i => id.withContext do dbg_trace s!"{id.name} d↦ {i.fvars} ⊢ {i.mvarIdPending.name}")
     -- dbg_trace s!"La mvar si chiama {mmmid.name}"
     mmmid.withContext do
      let tree ← proofTerm.toNDTreeM
      -- dbg_trace s!"Found proof term for {name}: {← exprInfo proofTerm}"
      dbg_trace s!"Found proof term for {name}:= {← exprInfo proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
      return { thmName := toString name, thmType := toString tyStr, treeJson := s!"{tree.toJson}" }

-- ══════════════════════════════════════════════════════════════════
-- WIDGET JAVASCRIPT
-- ══════════════════════════════════════════════════════════════════

@[widget_module]
def NDTreeJsonViewerWidget : Widget.Module where
  javascript := include_str "NDTreeJsonViewer.js"

-- =================
-- LOGICA
-- =================

syntax "and_e" term:max (ppSpace colGt (ident <|> hole))* : tactic

macro_rules
| `(tactic|and_e $h $l*) => `(tactic|refine And.casesOn $h ?_ <;> intros $l*)


-- ══════════════════════════════════════════════════════════════════
-- ATTIVA I WIDGET
-- ══════════════════════════════════════════════════════════════════
show_panel_widgets [NDTreeJsonViewerWidget]

set_option pp.proofs true

theorem foo2 (A : Prop) (h : A) : A := by
  exact h

theorem Andleft (P Q : Prop) (h : P ∧ Q) : P := by
 and_e h p _
 exact p

theorem Andright (P Q : Prop) (h : P ∧ Q) : Q := by
  and_e h _ q
  exact q

theorem AndIntro (P Q : Prop) (h1 : P) (h2 : Q) : P ∧ Q := by
  apply And.intro
  . exact h1
  . exact h2

theorem OrIntroLeft2 (P Q : Prop) (h : P) : P -> (P ∧ P ∨ Q) ∨ Q := by
  intro x
  apply Or.inl
  apply Or.inl
  apply And.intro x h

theorem OrIntroLeft (P Q : Prop) (h : P) : P ∨ Q := by
  apply Or.inl h

theorem OrIntroRight (P Q: Prop) (h : Q)  : P ∨ Q := by
  apply Or.inr h

theorem OrElim (P Q R : Prop) (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := by
  cases h1 with
  | inl p => apply h2 p
  | inr q => apply h3 q
#print OrElim

theorem NotIntro (P : Prop) (h : P → False) : ¬P := by
  apply Not.intro h

theorem NotElim (P : Prop) (h1 : ¬P) (h2 : P) : False := by
  apply h1 h2

theorem NotElim' (P : Prop) (h1 : ¬P) : P → False := by
  intro h2
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
