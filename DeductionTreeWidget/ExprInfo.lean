import Lean
open Lean Meta

partial def withAggressiveInstantiateMVars (e: Expr) (k: Expr → MetaM α) : MetaM α := do
 let e ← instantiateMVars e
 match e with
 | .app _ _ => do
    match e.withApp fun e a => (e, a) with
    | (.mvar mid, args) =>
       match (← getMCtx).dAssignment.find? mid with
       | some i =>
          if i.fvars.size == args.size then
           let mut lctx := ← getLCtx
           for fv in i.fvars, arg in args do
            let fvid := fv.fvarId!
            lctx := LocalContext.mkLetDecl lctx fvid (← i.mvarIdPending.withContext fvid.getUserName) (← i.mvarIdPending.withContext fvid.getType) arg
           withLCtx' lctx do
            withAggressiveInstantiateMVars (.mvar i.mvarIdPending) k
          else
           k e
       | none => k e
    | _ => k e
 | _ => k e


partial def exprInfo (e : Expr) : MetaM String := do
  withAggressiveInstantiateMVars e fun e => do
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
  | .lam n t b bi =>
    withLocalDecl n bi t fun fv => do
      let child := (b.instantiate1 fv)
      let tStr ← exprInfo t
      let displayName := n.toString
      let bStr ← exprInfo child
      return s!".lam {displayName} : ({tStr}) => ({bStr})"
  | .forallE n t b bi =>
    withLocalDecl n bi t fun fv => do
    let child := (b.instantiate1 fv)
    if e.isArrow then  -- CSC XXX TODO bug, reimplementare, violiamo l'invariante richiesto
      -- non dipendente: ignora il nome del binder
      return s!"({← exprInfo t}) → ({← exprInfo child})"
    else
      let tStr ← exprInfo t
      let bStr ← exprInfo b
      return s!"∀ {n} : ({tStr}), ({bStr})"
  | .letE n t v b nondep   =>
      let tStr ← exprInfo t
      let vStr ← exprInfo v
      let bStr ← exprInfo b
      if nondep then
        return s!"have {n} : ({tStr}) := ({vStr}); {bStr}"
      return s!".let {n} : ({tStr}) := ({vStr}); {bStr}"
  | .lit (.natVal n)  => return s!"Nat {n}"
  | .lit (.strVal s)  => return s!"Str {s}"
  | .mdata _ e        => exprInfo e
  | .proj tn idx s    =>
      return s!".proj {tn}.{idx} ({← exprInfo s})"
