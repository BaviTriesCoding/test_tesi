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
abbrev isCurrentGoal := Bool
abbrev Proof := String -- Nei nodi unhandled è la prova non riconosciuta

inductive NDTree where
  | leaf      : List (Name × NDTree) → Name → Formula → isDischarged → NDTree
  | node      : List (Name × NDTree) → Formula → Rule → List NDTree → NDTree
  | openNode  : List (Name × NDTree) → Formula → isCurrentGoal → NDTree
  | unhandled : NDTree
  deriving FromJson, ToJson, Server.RpcEncodable, BEq

def NDTree.isLeaf: NDTree → Bool
  | .leaf _ _ _ _ => true
  | _ => false

def NDTree.isNode : NDTree →  Bool
  | .node _ _ _ _ => true
  | _ => false

def NDTree.isOpenNode : NDTree → Bool
  | .openNode _ _ _ => true
  | _ => false

def NDTree.isUnhandled : NDTree → Bool
  | .unhandled => true
  | _ => false


abbrev Hyp := (Name × NDTree)

def Lean.Name.isHygName (n : Name) : Bool := if (n.toString.contains "_@" || n.toString.contains "_hyg") then true else false

partial def NDTree.toJson : NDTree → String
  | .leaf hypotheses name f isDischarged =>
    "{
      \"type\":\"leaf\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value⟩ =>
      "{" ++
        (if !name.isHygName then "\"name\":\"" ++ name.toString ++ "\"," else "")
        ++ "\"value\":" ++ value.toJson ++ "
      }") ++ "],"
      ++
      (if !name.isHygName then "\"name\":\"" ++ name.toString ++ "\"," else "")
      ++
      "\"formula\":\""++ f ++"\",
      \"isDischarged\":" ++ s!"{repr isDischarged}" ++ "
    }"
  | .node hypotheses f rule children =>
    "{
      \"type\":\"node\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value⟩ =>
      "{" ++
        (if !name.isHygName then "\"name\":\"" ++ name.toString ++ "\"," else "")
        ++ "\"value\":" ++ value.toJson ++ "
      }") ++ "],
      \"formula\":\"" ++ f ++ "\",
      \"rule\": \"" ++ rule ++ "\",
      \"children\": [" ++ ", ".intercalate (children.map toJson) ++ "]
    }"
  | .openNode hypotheses f isCurrentGoal =>
    "{
      \"type\":\"openNode\",
      \"hypotheses\": [" ++ ", ".intercalate (hypotheses.map fun ⟨name, value⟩ =>
      "{" ++
        (if !name.isHygName then "\"name\":\"" ++ name.toString ++ "\"," else "")
        ++ "\"value\":" ++ value.toJson ++ "
      }") ++ "],
      \"formula\":\"" ++ f ++ "\",
      \"isCurrentGoal\":" ++ s!"{repr isCurrentGoal}" ++ "
    }"
  | .unhandled  =>
    "{
      \"type\":\"unhandled\"
    }"


def isTreeDischarged (t : NDTree) : Bool :=
  match t with
  | .leaf hyps name formula _ =>
    hyps.foldl (fun res (name', value) =>
      match value, res with
      | _, true => true
      | .leaf _ _ formula' _ , false =>
        name == name' && formula == formula'
      | _, _ => false
    ) false
  | _ => false


def Lean.Expr.isSort1 (e: Expr) : Bool :=
  match e with
  | Expr.sort 1 => true
  | _ => false

def reprLCtx (hyps : List Hyp) : MetaM String := do
  return ", ".intercalate (hyps.map fun hyp =>
    match hyp with
    | (n, .leaf _ _ f _) => s!"{n} : {f}"
    | (n, .node _ f _ _) => s!"{n} : {f}"
    | _ => ""
  )

mutual
partial def getHypoteses (rootHyps : List Hyp := []) (isLHS : Bool := false) : MetaM (List Hyp) := do
  let list ← (← getLCtx).decls.foldlM (fun s i => do
    match s, i with
    | [], _ => return [.none]
    | _, none => return s
    | _, some d =>
        let t := (← inferType (.fvar d.fvarId))
        if (← inferType t).isSort1 then return s
        if rootHyps.contains (d.userName, (NDTree.leaf [] d.userName s!"{← ppExpr t}" false)) then
          return s
        match d.value? (allowNondep := true) with
        | none => do
          let leaf :NDTree := .leaf [] d.userName s!"{← ppExpr t}" (!isLHS && !(← rootHyps.foldlM (fun res h =>
            match res, h with
            | true, _ => return true
            | false, (name, .leaf _ _ f _) => return  name == d.userName && f == s!"{← ppExpr t}"
            | _, _ => return false
          ) false ))
          return s ++ [.some (d.userName, leaf)]
        | some v => do
          return s ++ [.some (d.userName, (← v.toNDTreeM (withHyp := false) (rootHyps := rootHyps)))])
    []

  return list.filterMap id


partial def Lean.Expr.toNDTreeM (e : Expr) (withHyp := true) (rootHyps : List Hyp := []) (currentGoal : Option MVarId := none) : MetaM NDTree := do
  withAggressiveInstantiateMVars e fun e => do
  let (fn, args') := e.withApp fun e a => (e, a.toList)
  let args ← args'.filterMapM (fun arg => do
    return match (← inferType (← inferType arg)) with
    | .sort (.succ _) => none
    | _ => some arg)
  /- -- debug purpose
  let fnPrintable := ← exprInfo fn
  let mut argsPrintable : List String := []
  for arg in args do
    argsPrintable := argsPrintable ++ [s!"{(← exprInfo arg)}"]
  --dbg_trace s!"{fnPrintable} : {argsPrintable}"
  -- -/
  let hyps ← if withHyp then getHypoteses (rootHyps := rootHyps) else pure []
  let formula := s!"{← ppExpr (← inferType e)}"
  match fn, args with
  -- ↓ casi normalmente impossibili ↓

  | (.forallE _ _ _ _ ), _  => throwError ".forallE unexpected in a proof"

  | (.bvar _), _            => throwError ".bvar unexpected in a proof"

  | (.sort _), _            => throwError ".sort unexpected in a proof"

  | (.lit _), _             => throwError ".lit unexpected in a proof"
  -- ↓ foglie ↓

  | (.const (.str _ n) _), [] => return .leaf hyps n.toName formula ( isTreeDischarged (.leaf hyps n.toName formula false))

  | (.fvar id), [] => do
      let decl ← Meta.getFVarLocalDecl (.fvar id)
      match decl.value? with
      | none => return .leaf hyps decl.userName (toString (← ppExpr decl.type)) ( isTreeDischarged (.leaf hyps decl.userName (toString (← ppExpr decl.type)) false))
      | some v => return ← v.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)


  | (.const `sorryAx _), _ => return .leaf hyps `sorryAx "sorry" false
  -- ↓ nodi aperti ↓

  | (.mvar mmmid), _ => do
    mmmid.withContext do
      match currentGoal with
      | none => return .openNode (← if withHyp then do getHypoteses (rootHyps := rootHyps) else pure []) formula false
      | some mvar => return .openNode (← if withHyp then do getHypoteses (rootHyps := rootHyps) else pure []) formula (mmmid == mvar)
  -- ↓ nodi ↓

  | (.letE n t v b _), _ => do
    withLetDecl n t v fun fv =>
      let b' := b.instantiate1 fv

        return ← b'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)

  | (.lam n t b bi), _ => do
    withLocalDecl n bi t fun fv => do
      let b := b.instantiate1 fv
      let ruleName := if (← inferType t).isProp then "→I" else "∀I"
      let child ← b.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
      return .node hyps s!"{← ppExpr (← inferType fn)}" ruleName [child]

  | (.fvar _), _::_ => do
    let baseNode := (← fn.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal))
    let (_, finalNode) ← args'.foldlM (
      fun (accApp, accNode) nextArg => do
      let newApp  := .app accApp nextArg
      match (← inferType (← inferType nextArg)) with
      | (.sort 0) =>
        let newNode := .node hyps s!"{← ppExpr (← inferType newApp)}" "→E" [accNode, (← nextArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal))]
        return (newApp, newNode)
      | (.sort (.succ 0)) =>
        let newNode := .node hyps s!"{← ppExpr (← inferType newApp)}" "∀E" [accNode]
        return (newApp, newNode)
      | _ =>
        let newNode := (← nextArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal))
        return (newApp, newNode)
    ) (fn, baseNode)
    return finalNode

  | (.const `And.intro _), arg0::arg1::_ =>
    return .node hyps formula "∧I" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]


  | (.const `And.casesOn _), andArg::(.lam n t (.lam n' t' b bi') bi)::_ => do
    withLocalDecl n bi t fun fv => do
      let b' := b.instantiate1 fv
      withLocalDecl n' bi' t' fun fv' => do
        let b'' := b'.instantiate1 fv'
        return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← b''.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `And.casesOn _), andArg::(.lam n t b bi)::_ => do
    withLocalDecl n bi t fun fv => do
      let b' := b.instantiate1 fv
      return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← b'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `And.casesOn _), andArg::arg0::_ => do
    return .node hyps formula "∧E" [← andArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]
  | (.const `And.left _), arg::_ =>
    return .node hyps formula "∧E₁" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `And.right _), arg::_ =>
    return .node hyps formula "∧E₂" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Or.inl _), arg::_ =>
    return .node hyps formula "∨I₁" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Or.inr _), arg::_ =>
    return .node hyps formula "∨I₂" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Or.casesOn _), orArg::(.lam nl tl bl bil)::(.lam nr tr br bir)::_ => do
    let childL ← withLocalDecl nl bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    let childR ← withLocalDecl nr bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), childL, childR]

  | (.const `Or.casesOn _), orArg::arg0::(.lam nr tr br bir)::_ => do
    let childR ← withLocalDecl nr bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), childR]

  | (.const `Or.casesOn _), orArg::(.lam nl tl bl bil)::arg1::_ => do
    let childL ← withLocalDecl nl bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "∨E" [← orArg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), childL, ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Not.intro _), arg::_ =>
    return .node hyps formula "¬I" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `absurd _), arg0::arg1::_ =>
    return .node hyps formula "¬E" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `False.elim _), arg::_ =>
    return .node hyps formula "⊥E" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Exists.intro _), arg::_ =>
    return .node hyps formula "∃I" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Exists.elim _), arg0::arg1::_ =>
    return .node hyps formula "∃E" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Exists.casesOn _), arg0::arg1::_ =>
    return .node hyps formula "∃E" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]


  | (.const `Iff.intro _), arg0::arg1::_ => do
    return .node hyps formula "↔I" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Iff.mp _), arg::_ => do
    return .node hyps formula "↔E₁" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  | (.const `Iff.mpr _), arg::_ => do
    return .node hyps formula "↔E₂" [← arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]

  /- -- stavo guardando i vari casi di utilizzo di Iff.intro e si usa sempre suppose manualmente, e `we need to prove A → B`, quindi direi di lasciarlo senza la semplificazione
  | (.const `Iff.intro _), (.lam nl tl bl bil)::(.lam nr tr br bir)::_ => do
    let childL ← withLocalDecl nl bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    let childR ← withLocalDecl nr bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "↔I" [childL, childR]

  | (.const `Iff.intro _), _::(.lam nr tr br bir)::_ => do
    let childR ← withLocalDecl nr bir tr fun fvr => do
      let br' := br.instantiate1 fvr
      br'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "↔I" [(NDTree.unhandled), childR]
    -- return .node hyps formula "↔I" [← arg0.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal), childR]

  | (.const `Iff.intro _), (.lam nl tl bl bil)::_::_ => do
    let childL ← withLocalDecl nl bil tl fun fvl => do
      let bl' := bl.instantiate1 fvl
      bl'.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
    return .node hyps formula "↔I" [childL, (NDTree.unhandled)]
    -- return .node hyps formula "↔I" [childL, ← arg1.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)]-/

  | fn, args => do
      let children ← args.mapM fun arg =>  arg.toNDTreeM (withHyp := withHyp) (rootHyps := rootHyps) (currentGoal := currentGoal)
      match fn with
      | .const (.str _ n) _ => return .node hyps formula s!"{n.toName}" (children)
      | _ => return .node hyps formula s!"{← ppExpr fn}" (children)

end

-- ══════════════════════════════════════════════════════════════════
-- RPC METHOD: GET TREE AS JSON
-- ══════════════════════════════════════════════════════════════════

structure DebugLogParams where
  msg : String
  deriving FromJson, ToJson

structure DebugLogResult where
  msg : String
  deriving FromJson, ToJson, Server.RpcEncodable

open Lean Server RequestM in
@[server_rpc_method]
def debugLog (p : DebugLogParams) : RequestM (RequestTask DebugLogResult) := do
  dbg_trace "[DEBUG] {p.msg}"
  asTask do return {msg := s!"Logged: {p.msg}"}


structure DeductionAtCursorParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure TreeAsJsonResult where
  thmName : String
  thmType : String
  treeJson : String
  deriving FromJson, ToJson, Server.RpcEncodable

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
    let mvar := item.tacticInfo.goalsAfter.head?
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
        if proofTerm.isSort1 then throwError s!"Il termine trovato non è una prova: {← exprInfo proofTerm} : {← ppExpr (← inferType proofTerm)}"
        let rootHyps ← getHypoteses (isLHS := true)
        let tree ← (proofTerm.toNDTreeM (rootHyps := rootHyps) (currentGoal := mvar))
        -- dbg_trace s!"{← exprInfo proofTerm}"
        -- dbg_trace s!"Found proof term for {name}: {← exprInfo proofTerm}"
        -- dbg_trace s!"Found proof term for {name}:= {← exprInfo proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
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
[_] gestione ex. 4 iff_e
[_] consistenza ex, 10 (usare barra vuota per le ipotesi che sono teoremi già dimostrati)
[_] in ExprInfo reimplementare e.isArrow perchè violiamo precondizione di non occorrenza delle bvar e quindi alcuni diventano forall; il bug sembra esserci anche per la resa dei nodi (ma può avere una causa diversa)
════════════════════════════════════════════════════════════════════
DONE:
[✓] a volte il JSON contiene caratteri non permessi (trovare la lista dei caratteri accettati) json non accetta tutti i caratteri escaped, quindi ho risolto eliminandoli dal json finale nel caso vengano prodotti. const validJSON = res.treeJson.replace(/[\x00-\x1F\x7F-\x9F]/g, '');
[✓] problema di taglia degli alberi, che sforano a sinistra
[✓] aggiungere un modo per visualizzare gli unhandled.
[✓] capire come gestire le foglie scaricate → struttura dati,
[✓] riconoscere il caso ¬i
[✓] riconoscere il caso ¬e
[✓] nel caso in cui ci siano più →E, vengono messe in una sola riga, ma bisogna renderle più di una.
[✓] gestione del caso have (creazione di alberi "separati")
[✓] gestisci il caso .const (ora unhandled)
[✓] set theory ex. 8 unexpected bound variable
[✓] refactoring del codice partendo dalla get_app_fn_args e poi facendo pattern matching doppio e profondo su testa e argomenti Nota: per iniziare usa unhandled in tutti i casi in cui i vari orElim etc. non sono come li vorresti; più avanti si può pensare a cosa fare nei casi residui
[✓] nel caso (ora sono due ma dopo la ristrutturazione del codice sarà 1) di una mvar,recuperare la lista delle ipotesi usando "reprLCtx" e non "hypotheses" perchè possonodifferire; si vedranno probabilmente cose discrepanze/cose strane (tombstones) e vedremo come gestirle
[✓] filtrare le ipotesi globali dalle ipotesi interne ai nodi
[✓] refactor grafico: le linee orizzontali degli alberi devono essere lunghe tanto quanto il massimo tra la larghezza del nodo padre e la larghezza del primo figlio.
[✓] capire che expr è set e farlo sparire
[✓] verificare se gli alberi sono esatti e ragionevoli
[✓] ∀ non testato
[✓] evitare di mostrare il namespace dentro i nomi
[✓] problemi nei nomi (es. set_theory.set†)
════════════════════════════════════════════════════════════════════
-/
