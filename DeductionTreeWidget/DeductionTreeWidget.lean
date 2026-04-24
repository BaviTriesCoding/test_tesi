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
 -- | open       : List NDTree → Formula → NDTree  -- lista di "ipotesi" alcune delle quali dimostrate e quindi sono alberelli (= le decls) + conclusione
 -- | leafthm : Name -> Formula? → NDTree  -- uso di un teorema (ovvero una .const e non una .fvar), una foglia che è un teorema di cui visualizzare solo il nome (e magari un tooltip con il tipo)
  | leaf      : Formula → isOpen → NDTree -- queste sono le .fvar
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

-- CSC: invece di usare exprInfo si può usare repr che è più verbosa, ma si capisce uguale
-- For debugging: it prints the low level details of the term (e.g. bvar vs fvar)
partial def exprInfo (e : Expr) : MetaM String := do
  match /-← instantiateMVars-/ e with
  | .bvar idx         => return s!".bvar {idx}"
  | .fvar _ =>
      match (← getLCtx).find? e.fvarId! with
      | some decl =>
         return s!".fvar {decl.userName}"
      | none =>
         return s!".fvar {repr e.fvarId!} UNBOUND"
  | .mvar id          => return s!".mvar {id.name}"
  | .sort lvl         => return s!".sort {lvl}"
  | .const name us    => return s!".const {name} {us}"
  | .app fn arg       =>
      return s!".app ({← exprInfo fn}) ({← exprInfo arg})"
  | .lam n t b _ =>
    let tStr ← exprInfo t
    let displayName := n.toString
    let bStr ← exprInfo b
    return s!".lam {displayName} : ({tStr}) => ({bStr})"
  | .forallE n t b _ =>
    if e.isArrow then  -- CSC XXX TODO bug, reimplementare, violiamo l'invariante richiesto
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

partial def withAggressiveInstantiateMVars (e: Expr) (k: Option Expr → MetaM α) : MetaM α := do
 let e ← instantiateMVars e
 match e with
 | .app _ _ => do
    match e.withApp fun e a => (e, a) with
    | (.mvar mid, args) =>
       match (← getMCtx).dAssignment.find? mid with
       | some i =>
          if i.fvars.size == args.size then
           let mut lctx := ← getLCtx
           let mut error := false
           for fv in i.fvars, arg in args do
            let fvid := fv.fvarId!
            match lctx.find? fvid with
            | none =>
              lctx := LocalContext.mkLetDecl lctx fvid (← i.mvarIdPending.withContext fvid.getUserName) (← i.mvarIdPending.withContext fvid.getType) arg
            | some _ =>
              dbg_trace s!"Instantiating twice the same delayed metavariable. Currently not supported."
              error := true
           if error then k none
           else
            withLCtx' lctx do
             withAggressiveInstantiateMVars (.mvar i.mvarIdPending) k
          else
           k none
       | none => k (some e)
    | _ => k (some e)
 | _ => k (some e)

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

partial def Lean.Expr.toNDTreeM (e : Expr) : MetaM NDTree := do
  /- for debugging
  -- dbg_trace s!"Processing: {← exprInfo e'}"
  -- dbg_trace s!"typed as {← ppExpr (← inferType e')}" -/
  withAggressiveInstantiateMVars e fun e' => do
  /- for debugging
  dbg_trace s!"Becomes: {← exprInfo e}"
  dbg_trace s!"typed as {← ppExpr (← inferType e')}"
  dbg_trace s!"Env: {← ppExpr (Expr.bvar 0)} {← ppExpr (Expr.bvar 1)} {← ppExpr (Expr.bvar 2)}"
  dbg_trace s!"-----------------------------------"-/
  match e' with
  | none => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"
  | some e =>
    match e with
    | .app _ _ => do
        let (fn, args) := e.withApp fun e a => (e, a)
        match fn with
        | .const ``sorryAx [] =>
          let resultType ← inferType e
          return .node [] s!"{← ppExpr resultType}" "sorry"
        | .mvar mid =>
          -- CSC: bug, in next line the args are lost; they should go in the NDTree as →E/∀E
          return .leaf s!"{← reprLCtx (verbose:=true) ((← getMCtx).getDecl mid).lctx}  ⊢ {← ppExpr (← inferType e)}" true  -- anche qui è open
        | _ =>
          let mut argList : List NDTree := []
          let (rulename, needshead) ← ruleNameOfApp fn
          for arg in args do
            if (← inferType (← inferType arg)).isProp then
              argList := argList ++ [← arg.toNDTreeM]
          if needshead then argList := (← fn.toNDTreeM)::argList
          let resultType ← inferType e
          return .node argList s!"{← ppExpr resultType}" s!"{rulename}"
    -- →I se il binder è una Prop (scarica un'assunzione)
    -- ∀I se il binder è un Type (introduce una variabile)
    | .lam n t b bi =>
        let lamType ← ppExpr (← inferType e)
        let tKind ← inferType t
        let ruleName := if tKind.isProp then "→I" else "∀I"
        withLocalDecl n bi t fun fv => do
         let child ← (b.instantiate1 fv).toNDTreeM
         return .node [child] s!"{lamType}" ruleName
    /-  XXX TODO codice bacato
    | .forallE n t b bi =>
        -- CSC: questo caso non può accadere se stiamo processando
        -- una prova p : T : Prop
        -- in quanto ∀... : sort_n : Type_m ≠ Prop
        -- Questo mostra però un problema: il widget dovrebbe provare a rendere
        -- l'albero sse la costante all'interno della quale siamo è veramente
        -- una prova, ovvero il tipo del tipo della costante è Prop
        -- Implementare questo check in getTreeAsJson
    | .proj _ _ e         => TODO -- CSC: questo può succedere
    -/
    | .letE _ _ v body _ => (body.instantiate1 v).toNDTreeM
    | .mdata _ e          => e.toNDTreeM
    | .fvar id => do
        let decl ← Meta.getFVarLocalDecl (.fvar id)
        return .leaf (toString (← ppExpr decl.type)) false
    | .mvar mid => return .leaf s!"{← reprLCtx (verbose:=true) ((← getMCtx).getDecl mid).lctx}  ⊢ {← ppExpr (← inferType e)}" true -- qui è open
    | e => return .unhandled s!"{← ppExpr e}" s!"{← ppExpr (← inferType e)}"

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
     /- for debugging
     metavarctx.decls.forM (fun id i => id.withContext do dbg_trace s!"{← reprLCtx (← getLCtx)} ⊢ {id.name} : {← exprInfo i.type}")
     metavarctx.eAssignment.forM (fun id e => id.withContext do dbg_trace s!"{← reprLCtx (← getLCtx)} ⊢ {id.name} e↦ {← exprInfo e}")
     metavarctx.dAssignment.forM (fun id i => id.withContext do dbg_trace s!"{← reprLCtx (← getLCtx)} ⊢ {id.name} d↦ {i.fvars} ⊢ {i.mvarIdPending.name}")
     -/
     -- dbg_trace s!"La mvar si chiama {mmmid.name}"
     mmmid.withContext do
      let tree ← proofTerm.toNDTreeM
      -- dbg_trace s!"Found proof term for {name}: {← exprInfo proofTerm}"
      -- dbg_trace s!"Found proof term for {name}:= {← exprInfo proofTerm} : {← ppExpr (← inferType proofTerm)} == {tyStr}"
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
- a) a volte il JSON contiene caratteri non permessi (trovare la lista dei caratteri accettati) ✓
    json non accetta tutti i caratteri escaped, quindi ho risolto eliminandoli dal json finale nel caso vengano prodotti.
    const validJSON = res.treeJson.replace(/[\x00-\x1F\x7F-\x9F]/g, '');
- c) verificare se gli alberi sono esatti e ragionevoli
- d) problema di taglia degli alberi, che sforano a sinistra
- e) capire come gestire le foglie scaricate
- f₁) riconoscere il caso ¬e ✓
- f₂) riconoscere il caso ¬i
- f₃) ∀ non testato




════════════════════════════════════════════════════════════════════
-/
