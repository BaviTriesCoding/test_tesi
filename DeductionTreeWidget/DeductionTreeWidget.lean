import DeductionTreeWidget.ExprInfo
import Lean
import Lean.Server.Rpc.Basic
open Lean Meta Server Widget exprInfo
-- ══════════════════════════════════════════════════════════════════
-- Natural Deduction Tree Type
-- ══════════════════════════════════════════════════════════════════

abbrev Formula := String -- Quello che c'è scritto nelle foglie
abbrev Rule := String -- ¬i, ∧e1, ∧e2, ∧i, ∨i1, ∨i2, ∨e, →i, →e, etc.
abbrev isDischarged := Bool --Il booleano è per capire se è una foglia aperta o scaricata
abbrev Proof := String -- Nei nodi unhandled è la prova non riconosciuta

inductive NDTree where
  | leaf      : List (Name × NDTree × isDischarged) → Name → Formula → isDischarged → NDTree                        -- .fvar
  | node      : List (Name × NDTree × isDischarged) → Formula → Rule → List NDTree → NDTree  -- .mvar
  | openNode  : List (Name × NDTree × isDischarged) → Formula → NDTree
  | unhandled : Proof → Formula → NDTree                        -- Per rappresentare i nodi che non siamo ancora in grado di gestire
  deriving FromJson, ToJson, Server.RpcEncodable

abbrev Hyp := (Name × NDTree × isDischarged)

partial def NDTree.toJson : NDTree → String
  | .leaf hypotheses name f isDischarged =>
    "{
      \"type\":\"leaf\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value, isDischarged⟩ =>
      "{
        \"name\":\"" ++ name.toString ++ "\",
        \"value\":" ++ value.toJson ++ ",
        \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
      }") ++ "],
      \"name\":\"" ++ name.toString ++ "\",
      \"formula\":\""++ f ++"\",
      \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
    }"
  | .node hypotheses f rule children =>
    "{
      \"type\":\"node\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value, isDischarged⟩ =>
      "{
        \"name\":\"" ++ name.toString ++ "\",
        \"value\":" ++ value.toJson ++ ",
        \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
      }") ++ "],
      \"formula\":\"" ++ f ++ "\",
      \"rule\": \"" ++ rule ++ "\",
      \"children\": [" ++ ", ".intercalate (children.map toJson) ++ "]
    }"
  | .openNode hypotheses f =>
    "{
      \"type\":\"openNode\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value, isDischarged⟩ =>
      "{
        \"name\":\"" ++ name.toString ++ "\",
        \"value\":" ++ value.toJson ++ ",
        \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
      }") ++ "],
      \"formula\":\"" ++ f ++ "\"
    }"
  | .unhandled p f =>
    "{
      \"type\":\"unhandled\",
      \"formula\":\"" ++ f ++ "\",
      \"unhandledProof\": \"" ++ p ++ "\"
    }"

partial def NDTree.toString (tree : NDTree) : String := tree.toJson

def Hyp.toString (h : Hyp) : String :=
  let (name, tree, isDischarged) := h
  s!"{if isDischarged then "[" else ""}{name} : {tree.toString}{if isDischarged then "]" else ""}"
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
def isNameInHyps (n : Name) (hyps : List Hyp) : Bool :=
  hyps.foldl (fun s (name, _, _) =>
    if !s then
      s || n == name
    else
      s
  ) false

mutual

partial def getHypoteses (G: LocalContext) (rootHyps : List Hyp := []) (setUndischarged := false) : MetaM (List Hyp) := do
  let list ← G.decls.foldlM (fun s i => do
    match s with
    | [] => return [.none]
    | _ =>
       match i with
       | none => return s
       | some d =>
          if (← inferType (Expr.fvar d.fvarId)).isProp then
            return s
          let isDisch := if setUndischarged then false else (!isNameInHyps d.userName rootHyps)
          match d.value? with
          | none => do
            return s ++ [.some (d.userName, (← (Expr.fvar d.fvarId).toNDTreeM (withHyp := false) (rootHyps := rootHyps)) ,isDisch)]
          | some v => do
            return s ++ [.some (d.userName, (← v.toNDTreeM (withHyp := false) (rootHyps := rootHyps)), isDisch)])
    []

  return list.filterMap id


partial def Lean.Expr.toNDTreeM (e : Expr) (withHyp := true) (rootHyps : List Hyp := []) : MetaM NDTree := do
  withAggressiveInstantiateMVars e fun e => do
  let (fn, args') := e.withApp fun e a => (e, a.toList)
  let args ← args'.filterMapM (fun arg => do if (← inferType arg).isProp then return none else return some arg)
  /- -- debug purpose
  let fnPrintable := ← exprInfo fn
  let mut argsPrintable : List String := []
  for arg in args do
    argsPrintable := argsPrintable ++ [s!"{(← exprInfo arg)}"]
  dbg_trace s!"{fnPrintable} : {argsPrintable}"
  -- -/
  let hyps ← if withHyp then getHypoteses (← getLCtx) (rootHyps := rootHyps) else pure []
  let formula := s!"{← ppExpr (← inferType e)}"
  match fn, args with
  -- ↓ casi normalmente impossibili ↓
  | (.forallE _ _ _ _ ), []  => throwError ".forallE unexpected in a proof"
  | (.bvar _), []            => throwError ".bvar unexpected in a proof"
  | (.sort _), []            => throwError ".sort unexpected in a proof"
  | (.lit _), []             => throwError ".lit unexpected in a proof"
  -- ↓ foglie ↓
  | (.const n _), [] => return .leaf hyps n.subHygName formula (!isNameInHyps n rootHyps)
  | (.fvar id), [] => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      -- let isDischarged := ((hypotheses.map fun ⟨n, _⟩ => n).contains decl.userName) -- utilizzando le decls, non è chiaro come dovrei distinguerle
      return .leaf hyps decl.userName.subHygName (toString (← ppExpr decl.type)) (!isNameInHyps decl.userName rootHyps)
  | (.const ``sorryAx _), _ => return .leaf hyps `sorryAx "sorry" false
  -- ↓ nodi aperti ↓
  | (.mvar mmmid), [] => do
      mmmid.withContext do
        return .openNode (← if withHyp then do getHypoteses (← getLCtx) (rootHyps := rootHyps) else pure []) formula
  -- ↓ nodi ↓
  | (.letE n t v b _), [] => do
    withLetDecl n.subHygName t v fun fv =>
      let b' := b.instantiate1 fv
      return ← b'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
  | (.lam n t b bi), [] => do
    withLocalDecl n.subHygName bi t fun fv => do
      let b := b.instantiate1 fv
      let ruleName := if (← inferType t).isProp then "→I" else "∀I"
      let child ← b.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
      return .node hyps s!"{← ppExpr (← inferType fn)}" ruleName [child]
  | (.fvar fid), arg::l => do
    -- nodo base: rappresenta (fvar arg)
    let baseApp  := .app (.fvar fid) arg
    let baseNode := .node hyps s!"{← ppExpr (← inferType baseApp)}" "→E" [(← fn.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)), (← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps))]
    -- fold: accumulatore = (expr corrente, nodo corrente)
    let (_, finalNode) ← l.foldlM (
      fun (accApp, accNode) nextArg => do
      let newApp  := .app accApp nextArg
      let newNode := .node hyps s!"{← ppExpr (← inferType newApp)}" "→E" [accNode, (← nextArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps))]
      return (newApp, newNode)
    ) (baseApp, baseNode)
    return finalNode

  | (.const `And.intro _), arg0::arg1::_ =>
    return .node hyps formula "∧I" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]

  | (.const `And.casesOn _), _::andArg::(.lam n t (.lam n' t' b bi') bi)::_ => do
    withLocalDecl n.subHygName bi t fun fv => do
      let b' := b.instantiate1 fv
      withLocalDecl n'.subHygName bi' t' fun fv' => do
        let b'' := b'.instantiate1 fv'
        return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← b''.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `And.casesOn _), _::andArg::(.lam n t b bi)::_ => do
    withLocalDecl n.subHygName bi t fun fv => do
      let b' := b.instantiate1 fv
      return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← b'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `And.casesOn _), _::andArg::arg0::_ => do
    return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `And.left _), arg::_ =>
    return .node hyps formula "∧E₁" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `And.right _), arg::_ =>
    return .node hyps formula "∧E₂" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Or.inl _), arg::_ =>
    return .node hyps formula "∨I₁" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Or.inr _), arg::_ =>
    return .node hyps formula "∨I₂" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Or.casesOn _), _::orArg::(.lam nl tl bl bil)::(.lam nr tr br bir)::_ => do
    let childL ← withLocalDecl nl.subHygName bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    let childR ← withLocalDecl nr.subHygName bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), childL, childR]
  | (.const `Or.casesOn _), _::orArg::arg0::(.lam nr tr br bir)::_ => do
    let childR ← withLocalDecl nr.subHygName bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), childR]
  | (.const `Or.casesOn _), _::orArg::(.lam nl tl bl bil)::arg1::_ => do
    let childL ← withLocalDecl nl.subHygName bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), childL, ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Not.intro _), arg::_ =>
    return .node hyps formula "¬I" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `absurd _), arg0::arg1::_ =>
    return .node hyps formula "¬E" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `False.elim _), arg::_ =>
    return .node hyps formula "⊥E" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Exists.intro _), arg::_ =>
    return .node hyps formula "∃I" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Exists.elim _), arg0::arg1::_ =>
    return .node hyps formula "∃E" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | (.const `Iff.intro _), (.lam nl tl bl bil)::(.lam nr tr br bir)::_ => do
    let childL ← withLocalDecl nl.subHygName bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    let childR ← withLocalDecl nr.subHygName bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "↔I" [childL, childR]
  | (.const `Iff.intro _), arg0::(.lam nr tr br bir)::_ => do
    let childR ← withLocalDecl nr.subHygName bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "↔I" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps), childR]
  | (.const `Iff.intro _), (.lam nl tl bl bil)::arg1::_ => do
    let childL ← withLocalDecl nl.subHygName bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
    return .node hyps formula "↔I" [childL, ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)]
  | fn, args => do
      let children ← args.mapM fun arg =>  arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps)
      return .node hyps formula s!"{← ppExpr fn}" (children)

end

-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD: GET TREE AS JSON
-- ══════════════════════════════════════════════════════════════════

-- Prints the names of the vars in the LocalContext
def reprLCtx (hyps : List Hyp) : MetaM String := do
  return ", ".intercalate (hyps.map fun hyp =>
    match hyp with
    | (n, .leaf _ _ f _, isDischarged) => s!"{if isDischarged then "[" else ""}{n} : {f}{if isDischarged then "]" else ""}"
    | (n, .node _ f _ _, isDischarged) => s!"{if isDischarged then "[" else ""}{n} : {f}{if isDischarged then "]" else ""}"
    | _ => ""
  )


open Lean Server RequestM in
@[server_rpc_method]
def debugLog (msg : String) : RequestM (RequestTask String) := do
  dbg_trace "[DEBUG] {msg}"
  asTask do return s!"Logged: {msg}"


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
        let rootHyps ← getHypoteses (← getLCtx) (setUndischarged := true)
        let tree ← (proofTerm.toNDTreeM (rootHyps := rootHyps))
        -- dbg_trace s!"Found proof term for {name}: {← exprInf proofTerm}"
        -- dbg_trace s!"Found proof term for {name}:= {← exprInf proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
        return { thmName := toString name, thmType := s!"{← reprLCtx rootHyps} ⊢ {← ppExpr (← inferType proofTerm)}", treeJson := tree.toJson }

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
- d₃) [✓] aggiungere un modo per visualizzare gli unhandled.
- e)  [✓] capire come gestire le foglie scaricate → struttura dati,
- f₁) [✓] riconoscere il caso ¬e ✓
- f₂) [✓] riconoscere il caso ¬i
- f₃) [_] ∀ non testato
- f₄) [✓] nel caso in cui ci siano più →E, vengono messe in una sola riga, ma bisogna renderle più di una.
- h)  [✓] gestione del caso have (creazione di alberi "separati")
- i)  [ ] in ExprInfo reimplementare e.isArrow perchè violiamo precondizione
          di non occorrenza delle bvar e quindi alcuni diventano forall;
          il bug sembra esserci anche per la resa dei nodi (ma può avere una causa diversa)
- l)  [ ] gestisci il caso .const (ora unhandled)
- m)  [✓] set theory ex. 8 unexpected bound variable
- n)  [✓] refactoring del codice partendo dalla get_app_fn_args e poi facendo pattern matching
          doppio e profondo su testa e argomenti
          Nota: per iniziare usa unhandled in tutti i casi in cui i vari orElim etc. non sono
          come li vorresti; più avanti si può pensare a cosa fare nei casi residui
- o)  [✓] nel caso (ora sono due ma dopo la ristrutturazione del codice sarà 1) di una mvar,
          recuperare la lista delle ipotesi usando "reprLCtx" e non "hypotheses" perchè possono
          differire; si vedranno probabilmente cose discrepanze/cose strane (tombstones) e
          vedremo come gestirle
════════════════════════════════════════════════════════════════════
-/
