import DeductionTreeWidget.ExprInfo
import Lean
open Lean Meta Server Widget exprInfo
-- ══════════════════════════════════════════════════════════════════
-- Natural Deduction Tree Type
-- ══════════════════════════════════════════════════════════════════

abbrev Formula := String -- Quello che c'è scritto nelle foglie
abbrev ProofMethod := String -- ¬i, ∧e1, ∧e2, ∧i, ∨i1, ∨i2, ∨e, →i, →e, etc.
abbrev isDischarged := Bool --Il booleano è per capire se è una foglia aperta o scaricata
abbrev Proof := String -- Nei nodi unhandled è la prova non riconosciuta
inductive NDTree where
-- | open       : List NDTree → Formula → NDTree  -- lista di "ipotesi" alcune delle quali dimostrate e quindi sono alberelli (= le decls) + conclusione
-- | leafthm : Name -> Formula? → NDTree  -- uso di un teorema (ovvero una .const e non una .fvar), una foglia che è un teorema di cui visualizzare solo il nome (e magari un tooltip con il tipo)
  | leaf      : Formula → isDischarged → NDTree -- queste sono le .fvar
  | node      : List NDTree → Formula → ProofMethod → List NDTree → NDTree -- La stringa è per il nome del teorema o della regola usata
  | unhandled : Proof → Formula → NDTree                        -- Per rappresentare i nodi che non siamo ancora in grado di gestire
  deriving FromJson, ToJson, Server.RpcEncodable

def NDTree.toJson : NDTree → String
  | .leaf f isDischarged =>
    "{
      \"formula\":\""++ f ++"\",
      \"isDischarged\":\"" ++ s!"{repr isDischarged}" ++ "\"
    }"
  | .node hypotesis f rule children =>
      "{
        \"formula\":\"" ++ f ++ "\",
        \"rule\": \"" ++ rule ++ "\",
        \"hypotesis\": [" ++ String.intercalate ", " (hypotesis.map toJson) ++ "],
        \"children\": [" ++ String.intercalate ", " (children.map toJson) ++ "]
      }"
  | .unhandled p f =>
    "{
      \"formula\":\"" ++ f ++ "\",
      \"unhandledProof\": \"" ++ p ++ "\"
    }"

def NDTree.toString (tree : NDTree) : String := tree.toJson

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
    match fnType with
    | .app (.const ``Not []) (.fvar _) => return ("¬E", true)  -- P → False applicata a P
    | .forallE _ _ _ _ =>
      if fnType.isArrow then return ("→E", true)   -- P → Q applicata a P
      else return ("∀E", false)                     -- ∀ x, P x applicata a x

    | _ => return (s!"{← ppExpr e}", true)

mutual

partial def handleSorry (e : Expr) : MetaM NDTree := do
  let resultType ← inferType e
  return .leaf s!"{← ppExpr resultType}" true

partial def handleOrElim (e : Expr) (hypotesis : List NDTree) : MetaM NDTree := do
  let (_, args) := e.withApp fun e a => (e, a)
  let children ← args.filterMapM fun arg => do
    if (← inferType (← inferType arg)).isProp then
      match arg with
      | .lam n t b bi =>
        if (← inferType t).isProp then
          withLocalDecl n bi t fun fv => do
            -- dbg_trace s!"aggiungo ipotesi: {← ppExpr (fv)} : {← ppExpr t}"
            let child ← (b.instantiate1 fv).toNDTreeM ([← fv.toNDTreeM] ++ hypotesis)
            return some child
        else
          return some (← arg.toNDTreeM )
      | _ =>
        return some (← arg.toNDTreeM)
    else
      return none
  let resultType ← inferType e
  return .node hypotesis s!"{← ppExpr resultType}" "∨E" children.toList
-- appunto: per gestire i →e multipli, devo controllare se è una forallE con isArrow (quindi un'implicazione) e mettere come argomento solo il primo argomento. Da lì genero il prossimo expr come il body del forall.

partial def Lean.Expr.toNDTreeM (e : Expr) (hypotesis : List NDTree := []) : MetaM NDTree := do
  withAggressiveInstantiateMVars e fun e => do
  /- for debugging -/
  dbg_trace s!"═════════════════════════════════════════════════════════════════════════"
  dbg_trace s!"Processing: {← exprInfo e}"
  dbg_trace s!"typed as {← ppExpr (← inferType e)}"
  -- dbg_trace s!"Becomes: {← exprInfo e}"
  -- dbg_trace s!"typed as {← ppExpr (← inferType e')}"
  -- dbg_trace s!"Env: {← ppExpr (Expr.bvar 0)} {← ppExpr (Expr.bvar 1)} {← ppExpr (Expr.bvar 2)}"
  match e with
  | .app _ _ => do
      let (fn, args) := e.withApp fun e a => (e, a)
      match fn with
      | .const `sorryAx [] => return ← handleSorry e
      | .const `Or.casesOn [] => return ← handleOrElim e hypotesis
      | .mvar _ => return .leaf s!"{← ppExpr (← inferType e)}" true -- anche qui è open
      | _ =>
        let mut argList : List NDTree := []
        let (rulename, needshead) ← ruleNameOfApp fn
        for arg in args do
          if (← inferType (← inferType arg)).isProp then
            argList := argList ++ [← arg.toNDTreeM hypotesis]
        if needshead then argList := (← fn.toNDTreeM hypotesis)::argList
        let resultType ← inferType e
        return .node hypotesis s!"{← ppExpr resultType}" s!"{rulename}" argList

  -- →I se il binder è una Prop (scarica un'assunzione)
  -- ∀I se il binder è un Type (introduce una variabile)
  | .lam n t b bi =>
    let eType ← inferType e  -- tipo dell'intera espressione, NON ridotto
    dbg_trace s!"eType = {← exprInfo eType}"
    match eType with
    | .app (.const ``Not []) (.fvar _) =>
      -- È ¬P: il tipo è `Not P`, non `P → False`
      let tKind ← inferType t
      let ruleName := if tKind.isProp then "¬I" else "∀I"
      withLocalDecl n bi t fun fv => do
        let lamType ← ppExpr eType  -- mostrerà "¬P" e non "P → False"
        let child ← (b.instantiate1 fv).toNDTreeM ([← fv.toNDTreeM] ++ hypotesis)
        return .node hypotesis s!"{lamType}" s!"{ruleName}" [child]
    | _ =>
      -- È →I o ∀I
      let lamType ← ppExpr eType
      let tKind ← inferType t
      let ruleName := if tKind.isProp then "→I" else "∀I"
      withLocalDecl n bi t fun fv => do
        let child ← (b.instantiate1 fv).toNDTreeM ([← fv.toNDTreeM] ++ hypotesis)
        return .node hypotesis s!"{lamType}" s!"{ruleName}" [child]

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
  | .mdata _ e          => e.toNDTreeM hypotesis
  | .fvar id => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      return .leaf (toString (← ppExpr decl.type)) false
  | .mvar _ => return .node hypotesis s!"{← ppExpr (← inferType e)}" "" [] -- qui è open
  | e => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"
  where
    isHygienicName (n : Name) : Bool :=
      n.toString.contains "_@" || n.toString.contains "_hyg"
end
-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD: GET TREE AS JSON
-- ══════════════════════════════════════════════════════════════════

def reprInfoLCtx (G: LocalContext) : Format :=
 G.decls.foldl
  (fun s i =>
    match i with
    | none => s
    | some d =>
       /-s!"{s} {repr d.userName}({repr d.fvarId})"-/
       s!"{s} {repr d.userName}")
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
     /- for debugging -/
     -- metavarctx.decls.forM (fun id i => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} : { repr i.type}")
     -- metavarctx.eAssignment.forM (fun id e => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} e↦ {repr e}")
     -- metavarctx.dAssignment.forM (fun id i => id.withContext do dbg_trace s!"{reprLCtx (← getLCtx)} ⊢ {id.name} d↦ {i.fvars} ⊢ {i.mvarIdPending.name}")
     /- -/
     -- dbg_trace s!"La mvar si chiama {mmmid.name}"
     mmmid.withContext do
      let tree ← proofTerm.toNDTreeM
      -- dbg_trace s!"Found proof term for {name}: {← exprInf proofTerm}"
      -- dbg_trace s!"Found proof term for {name}:= {← exprInf proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
      return { thmName := toString name, thmType := toString tyStr, treeJson := s!"{tree.toJson}" }

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
- d₁) [_] problema di taglia degli alberi, che sforano a sinistra
- d₂) [_] refactor grafico: le linee orizzontali degli alberi devono essere lunghe tanto quanto il massimo tra la larghezza del nodo padre e la larghezza del primo figlio.
- d₃) [_] aggiungere un modo per visualizzare gli unhandled.
- e)  [_] capire come gestire le foglie scaricate → struttura dati,
- f₁) [✓] riconoscere il caso ¬e ✓
- f₂) [_] riconoscere il caso ¬i
- f₃) [_] ∀ non testato
- f₄) [_] nel caso in cui ci siano più →E, vengono messe in una sola riga, ma bisogna renderle più di una.
- h)  [_] gestione del caso have (creazione di alberi "separati")



════════════════════════════════════════════════════════════════════
-/
