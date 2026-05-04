import DeductionTreeWidget.ExprInfo
import Lean
open Lean Meta Server Widget exprInfo
-- ══════════════════════════════════════════════════════════════════
-- Natural Deduction Tree Type
-- ══════════════════════════════════════════════════════════════════

abbrev Formula := String -- Quello che c'è scritto nelle foglie
abbrev Rule := String -- ¬i, ∧e1, ∧e2, ∧i, ∨i1, ∨i2, ∨e, →i, →e, etc.
abbrev isDischarged := Bool --Il booleano è per capire se è una foglia aperta o scaricata
abbrev Proof := String -- Nei nodi unhandled è la prova non riconosciuta

inductive NDTree where
  | leaf      : Name → Formula → isDischarged → NDTree                        -- .fvar
  | node      : List (Name × NDTree) → Formula → Rule → List NDTree → NDTree  -- .mvar
  | openNode  : List (Name × NDTree) → Formula → NDTree
  | unhandled : Proof → Formula → NDTree                        -- Per rappresentare i nodi che non siamo ancora in grado di gestire
  deriving FromJson, ToJson, Server.RpcEncodable

abbrev Hyp := (Name × NDTree)


partial def NDTree.toJson : NDTree → String
  | .leaf name f isDischarged =>
    "{
      \"type\":\"leaf\",
      \"name\":\"" ++ name.toString ++ "\",
      \"formula\":\""++ f ++"\",
      \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
    }"
  | .node hypotheses f rule children =>
    "{
      \"type\":\"node\",
      \"formula\":\"" ++ f ++ "\",
      \"rule\": \"" ++ rule ++ "\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value⟩ =>
      "{
        \"name\":\"" ++ name.toString ++ "\",
        \"value\":" ++ value.toJson ++ "
      }") ++ "],
      \"children\": [" ++ ", ".intercalate (children.map toJson) ++ "]
    }"
  | .openNode hypotheses f =>
    "{
      \"type\":\"openNode\",
      \"formula\":\"" ++ f ++ "\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value⟩ =>
      "{
        \"name\":\"" ++ name.toString ++ "\",
        \"value\":" ++ value.toJson ++ "
      }") ++ "]
    }"
  | .unhandled p f =>
    "{
      \"type\":\"unhandled\",
      \"formula\":\"" ++ f ++ "\",
      \"unhandledProof\": \"" ++ p ++ "\"
    }"

partial def NDTree.toString (tree : NDTree) : String := tree.toJson
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
  | ``Or.casesOn   => "∨E"
  | ``Not.intro    => "¬I"
  | ``absurd       => "¬E"
  | ``False.elim   => "⊥E"
  | ``Exists.intro => "∃I"
  | ``Exists.elim  => "∃E"
  | other          => other.toString

-- Per le app: se fn è una costante nota, usa il mapping.
-- Altrimenti, controlla il tipo di fn per capire se è →E o ∀E.
def ruleNameOfApp (e : Expr) : MetaM (String × Bool) := do
  match ← instantiateMVars e with
  | .const name _ => return (ruleNameOf name, false)
  | _ =>
    let fnType ← inferType e
    -- dbg_trace s!"ruleNameOfApp: fnType = {← exprInfo fnType}"
    -- dbg_trace s!"ruleNameOfApp: fnType = {← exprInfo fnType}"
    match fnType with
    | .app (.const ``Not []) (.fvar _) => return ("¬E", true)  -- P → False applicata a P
    | .forallE _ _ _ _ =>
      if fnType.isArrow then return ("→E", true)   -- P → Q applicata a P
      else return ("∀E", false)                     -- ∀ x, P x applicata a x

    | _ => return (s!"{← ppExpr e}", true)

mutual

partial def handleSorry (e : Expr) : MetaM NDTree := do
  let resultType ← inferType e
  return .leaf ``sorryAx s!"{← ppExpr resultType}" false

partial def handleOrElim (e : Expr) (hypotheses : List Hyp) : MetaM NDTree := do
  let (_, args) := e.withApp fun e a => (e, a)
  let children ← args.filterMapM fun arg => do
    if (← inferType (← inferType arg)).isProp then
      match arg with
      | .lam n t b bi =>
        if (← inferType t).isProp then
          withLocalDecl n bi t fun fv => do
            -- dbg_trace s!"aggiungo ipotesi: {← ppExpr (fv)} : {← ppExpr t}"
            let child ← (b.instantiate1 fv).toNDTreeM ([(n,← fv.toNDTreeM)] ++ hypotheses)
            return some child
        else
          return some (← arg.toNDTreeM )
      | _ =>
        return some (← arg.toNDTreeM)
    else
      return none
  let resultType ← inferType e
  return .node hypotheses s!"{← ppExpr resultType}" "∨E" children.toList
-- appunto: per gestire i →e multipli, devo controllare se è una forallE con isArrow (quindi un'implicazione) e mettere come argomento solo il primo argomento. Da lì genero il prossimo expr come il body del forall.

partial def Lean.Expr.toNDTreeM (e : Expr) (hypotheses : List Hyp := []) : MetaM NDTree := do
  withAggressiveInstantiateMVars e fun e => do
  /- for debugging -/
  -- dbg_trace s!"═════════════════════════════════════════════════════════════════════════"
  -- dbg_trace s!"Processing: {← exprInfo e}"
  -- dbg_trace s!"typed as {← ppExpr (← inferType e)}"
  -- dbg_trace s!"Becomes: {← exprInfo e}"
  -- dbg_trace s!"typed as {← ppExpr (← inferType e')}"
  -- dbg_trace s!"Env: {← ppExpr (Expr.bvar 0)} {← ppExpr (Expr.bvar 1)} {← ppExpr (Expr.bvar 2)}"
  match e with
  | .app _ _ => do
      let (fn, args) := e.withApp fun e a => (e, a)
      -- dbg_trace s!"ho {args.size} argomenti applicati a {← exprInfo fn}"
      match fn with
      | .const ``sorryAx [] => return ← handleSorry e
      | .const ``Or.casesOn [] => return ← handleOrElim e hypotheses
      | .mvar _ => return .openNode hypotheses s!"{← ppExpr (← inferType e)}" -- anche qui è open
      | .const name _ =>
        let mut argList : List NDTree := []
        for arg in args do
          if (← inferType (← inferType arg)).isProp then
            argList := [← arg.toNDTreeM hypotheses] ++ argList
        let resultType ← inferType e
        return .node hypotheses s!"{← ppExpr resultType}" (ruleNameOf name) argList
      | _ =>
        -- NON usare args: prendi solo l'ultimo argomento
        let f   := e.appFn!   -- es: (.app h p)
        let arg := e.appArg!  -- es: q
        let fTy ← inferType f
        let resultType ← inferType e
        if fTy.isArrow then
          -- →E: due premesse, f ricorso darà il nodo intermedio
          let fTree   ← f.toNDTreeM hypotheses    -- ricorre su (.app h p) → altro →E
          let argTree ← arg.toNDTreeM hypotheses  -- q : Q
          return .node hypotheses s!"{← ppExpr resultType}" "→E" [fTree, argTree]
        else
          match fTy with
          | .forallE _ _ _ _ =>
            -- ∀E: arg è un termine, non una Prop
            let fTree ← f.toNDTreeM hypotheses
            return .node hypotheses s!"{← ppExpr resultType}" "∀E" [fTree]
          | _ =>
            -- Fallback per casi non gestiti
            let (rulename, needshead) ← ruleNameOfApp fn
            let mut argList : List NDTree := []
            for arg in args do
              if (← inferType (← inferType arg)).isProp then
                argList :=  [← arg.toNDTreeM hypotheses] ++ argList
            if needshead then argList := (← fn.toNDTreeM hypotheses) :: argList
            return .node hypotheses s!"{← ppExpr resultType}" rulename argList

  -- →I se il binder è una Prop (scarica un'assunzione)
  -- ∀I se il binder è un Type (introduce una variabile)
  | .lam n t b bi =>
      match (← inferType b) with
      | .const `False [] =>
        let tKind ← inferType t
        let ruleName := if tKind.isProp then "¬I" else "∀I"
        withLocalDecl n bi t fun fv => do
          let lamType ← ppExpr (Expr.app (Expr.const `Not  []) (← inferType fv))
          -- dbg_trace s!"aggiungo ipotesi: {← ppExpr (fv)} : {← ppExpr t}"
          let child ← (b.instantiate1 fv).toNDTreeM ([(n, ← fv.toNDTreeM)] ++ hypotheses)
          return .node hypotheses s!"{lamType}" s!"{ruleName}" [child]
      | _ =>
        let lamType ← ppExpr (← inferType e)  -- CSC: devi farlo PRIMA di withLocalDecl per non catturare la var
        let tKind ← inferType t
        let ruleName := if tKind.isProp then "→I" else "∀I"
        withLocalDecl n bi t fun fv => do
          -- dbg_trace s!"aggiungo ipotesi: {← ppExpr (fv)} : {← ppExpr t}"
          let child ← (b.instantiate1 fv).toNDTreeM ([(n,← fv.toNDTreeM)] ++ hypotheses)
          return .node hypotheses s!"{lamType}" s!"{ruleName}" [child]
  | .proj _ _ e         => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"
  | .forallE _ _ _ _ => throwError ".forallE unexpected in a proof"
  | .sort _ => throwError ".sort unexpected in a proof"
  | .bvar _ => throwError ".bvar unexpected in a proof"
  | .lit _ => throwError ".lit unexpected in a proof"
  | .letE name _ value body _ => do
    return ← (body.instantiate1 value).toNDTreeM ([(name,← value.toNDTreeM)] ++ hypotheses)
  | .mdata _ e          => e.toNDTreeM hypotheses
  | .fvar id => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      let isDischarged := ((hypotheses.map fun ⟨n, _⟩ => n).contains decl.userName)
      return .leaf decl.userName (toString (← ppExpr decl.type)) isDischarged
  | .mvar _ => return .openNode hypotheses s!"{← ppExpr (← inferType e)}" -- qui è open
  | .const _ _ => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"
end
-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD: GET TREE AS JSON
-- ══════════════════════════════════════════════════════════════════

-- Prints the names of the varsin the LocalContext
def reprLCtx (G: LocalContext) (verbose := false) : MetaM Format :=
 G.decls.foldlM
  (fun s i => do
    match s, verbose with
    | .nil, true => return " " -- quick&dirty hack to skip the recursive constant name
    | _, _ =>
       match i with
       | none => return s
       | some d =>
          -- s!"{s} {repr d.userName}({repr d.fvarId})"
          if verbose then
           let v : MetaM Format :=
            match d.value? (allowNondep := true) with
            | .none => return Format.nil
            | .some v => return ":=" ++ (← ppExpr v)
           let ty ← ppExpr d.type
           return s!"{s} ({repr d.userName}:{ty}{← v})"
          else
           return s!"{s} {repr d.userName}")
     .nil

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
    -- let info ← try getConstInfo name catch _ => throwThe RequestError ⟨.invalidParams, s!"Costante '{name}' non trovata"⟩
    -- let tyStr ← ppExpr info.type
    let metavarctx := item.tacticInfo.mctxAfter
    withMCtx metavarctx do
      let younger : Name -> Name -> Bool
      | .num _ 0, .num _ _ => false
      | .num _ n, .num _ m => n < m
      | _, _ => false
      let mmmid := metavarctx.eAssignment.foldl (fun m d _ => if younger m.name d.name then m else d)  (MVarId.mk (.num (.anonymous) 0))
      let proofTerm := Expr.mvar mmmid
      /- for debugging -/
      -- metavarctx.decls.forM (fun id i => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} : { repr i.type}")
      -- metavarctx.eAssignment.forM (fun id e => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} e↦ {repr e}")
      -- metavarctx.dAssignment.forM (fun id i => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} d↦ {i.fvars} ⊢ {i.mvarIdPending.name}")
      /- -/
      -- dbg_trace s!"La mvar si chiama {mmmid.name}"
      mmmid.withContext do
        if !(← inferType (← inferType proofTerm)).isProp then throwError s!"Il termine trovato non è una prova: {← exprInfo proofTerm} : {← ppExpr (← inferType proofTerm)}"
        let tree ← proofTerm.toNDTreeM
        -- dbg_trace s!"Found proof term for {name}: {← exprInf proofTerm}"
        -- dbg_trace s!"Found proof term for {name}:= {← exprInf proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
        return { thmName := toString name, thmType := s!"{← ppExpr (← inferType proofTerm)}", treeJson := s!"{tree.toJson}" }

-- ══════════════════════════════════════════════════════════════════
-- WIDGET JAVASCRIPT
-- ══════════════════════════════════════════════════════════════════

@[widget_module]
def NDTreeJsonViewerWidget : Widget.Module where
  javascript := include_str "NDTreeJsonViewer.js"

/-
═══════════════════════════════════════════════════════════════════
TODO:
- a)  [✓] a volte il JSON contiene caratteri non permessi (trovare la lista dei caratteri accettati)
    json non accetta tutti i caratteri escaped, quindi ho risolto eliminandoli dal json finale nel caso vengano prodotti.
    const validJSON = res.treeJson.replace(/[\x00-\x1F\x7F-\x9F]/g, '');
- c)  [_] verificare se gli alberi sono esatti e ragionevoli
- d₁) [✓] problema di taglia degli alberi, che sforano a sinistra
- d₂) [_] refactor grafico: le linee orizzontali degli alberi devono essere lunghe tanto quanto il massimo tra la larghezza del nodo padre e la larghezza del primo figlio.
- d₃) [_] aggiungere un modo per visualizzare gli unhandled.
- e)  [_] capire come gestire le foglie scaricate → struttura dati,
- f₁) [✓] riconoscere il caso ¬e ✓
- f₂) [✓] riconoscere il caso ¬i
- f₃) [_] ∀ non testato
- f₄) [✓] nel caso in cui ci siano più →E, vengono messe in una sola riga, ma bisogna renderle più di una.
- h)  [✓] gestione del caso have (creazione di alberi "separati")
- i)  [ ] in ExprInfo reimplementare e.isArrow perchè violiamo precondizione
          di non occorrenza delle bvar e quindi alcuni diventano forall;
          il bug sembra esserci anche per la resa dei nodi (ma può avere una causa diversa)
- l)  [ ] gestisci il caso .const (ora unhandled)
════════════════════════════════════════════════════════════════════
-/
