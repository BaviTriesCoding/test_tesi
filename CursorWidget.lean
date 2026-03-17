import Lean
open Lean Widget

structure GetTypeParams where
  /-- Name of a constant to get the type of. -/
  name : Name
  /-- Position of our widget instance in the Lean file. -/
  pos : Lsp.Position
  deriving FromJson, ToJson

structure GetTypeAtCursorParams where
  /-- Position of the cursor in the Lean file. -/
  cursorPos : Lsp.Position
  deriving FromJson, ToJson

structure ProofNode where
  /-- Tactic applied -/
  tactic : String
  /-- Goals before applying tactic -/
  goalsBefore : Array String
  /-- Goals after applying tactic -/
  goalsAfter : Array String
  /-- Hypotheses at this point -/
  hypotheses : Array String
  /-- Proof terms (lambda terms) for goals before -/
  proofTermsBefore : Array String
  /-- Proof terms (lambda terms) for goals after -/
  proofTermsAfter : Array String
  /-- Line number -/
  line : Nat
  /-- Depth level in proof tree -/
  depth : Nat
  deriving Server.RpcEncodable

structure GetTypeAtCursorResult where
  /-- The name of the symbol found at the cursor position. -/
  symbolName : String
  /-- The type/value of the symbol. -/
  code : CodeWithInfos
  /-- Complete proof term (lambda term) of the theorem -/
  completeLambdaTerm : String
  /-- Proof tree nodes up to cursor -/
  proofTree : Array ProofNode
  deriving Server.RpcEncodable

open Server RequestM in
@[server_rpc_method]
def getType (params : GetTypeParams) : RequestM (RequestTask CodeWithInfos) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      let name ← resolveGlobalConstNoOverloadCore params.name
      let c ← try getConstInfo name
        catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
      match c with
        | ConstantInfo.thmInfo t => Widget.ppExprTagged t.value
        | _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩

open Server RequestM in
@[server_rpc_method]
def getTypeAtCursor (params : GetTypeAtCursorParams) : RequestM (RequestTask GetTypeAtCursorResult) :=
  withWaitFindSnapAtPos params.cursorPos fun snap => do
    let text ← readDoc
    let fileMap := text.meta.text

    runTermElabM snap do
      let cursorLine := params.cursorPos.line

      -- Prima passata: trova la costante e raccogli le TacticInfo
      let (result, tacticInfos) := snap.infoTree.foldInfo
        (init := (none, #[]))
        fun _ctx info (acc : Option (Name × Expr) × Array (Elab.TacticInfo × Lsp.Position)) =>
          let (constOpt, infos) := acc

          -- Cerca la costante se non ancora trovata
          let newConst := match constOpt with
          | some _ => constOpt
          | none =>
            match info with
            | .ofTermInfo ti =>
              match ti.expr with
              | .const name _ => some (name, ti.expr)
              | _ => none
            | _ => none

          -- Raccogli le TacticInfo con la loro posizione
          let newInfos := match info with
          | .ofTacticInfo ti =>
            if let some pos := info.pos? then
              let lspPos := FileMap.utf8PosToLspPos fileMap pos
              if lspPos.line <= cursorLine then
                infos.push (ti, lspPos)
              else
                infos
            else
              infos
          | _ => infos

          (newConst, newInfos)

      -- Seconda passata: formatta i goal con operazioni monadiche
      let mut proofTree : Array ProofNode := #[]
      for (ti, lspPos) in tacticInfos do
        -- Formatta i goal before
        let goalsBefore ← ti.goalsBefore.toArray.mapM fun goal => do
          let goalFmt ← Meta.ppGoal goal
          return toString goalFmt

        -- Formatta i goal after
        let goalsAfter ← ti.goalsAfter.toArray.mapM fun goal => do
          let goalFmt ← Meta.ppGoal goal
          return toString goalFmt

        -- Estrai i proof terms (lambda terms) dai goal
        let proofTermsBefore ← ti.goalsBefore.toArray.mapM fun goal => do
          let mvarDecl ← goal.getDecl
          let typ := mvarDecl.type
          let typeFmt ← Meta.ppExpr typ
          return toString typeFmt

        let proofTermsAfter ← ti.goalsAfter.toArray.mapM fun goal => do
          let mvarDecl ← goal.getDecl
          let typ := mvarDecl.type
          let typeFmt ← Meta.ppExpr typ
          return toString typeFmt

        proofTree := proofTree.push {
          tactic := toString ti.stx
          goalsBefore := goalsBefore
          goalsAfter := goalsAfter
          hypotheses := #[]
          proofTermsBefore := proofTermsBefore
          proofTermsAfter := proofTermsAfter
          line := lspPos.line
          depth := 0
        }

      match result with
      | some (name, expr) =>
        let c ← try getConstInfo name
          catch _ => throwThe RequestError ⟨.invalidParams, s!"Cannot get info for constant '{name}'"⟩

        let codeResult ← match c with
          | .thmInfo t => Widget.ppExprTagged t.value
          | .defnInfo d => Widget.ppExprTagged d.value
          | .axiomInfo a => Widget.ppExprTagged a.type
          | .opaqueInfo o => Widget.ppExprTagged o.value
          | _ => Widget.ppExprTagged expr

        -- Estrai il lambda-termine completo della dimostrazione
        let completeLambdaTerm ← match c with
          | .thmInfo t => do
            let proofFmt ← Meta.ppExpr t.value
            pure (toString proofFmt)
          | .defnInfo d => do
            let proofFmt ← Meta.ppExpr d.value
            pure (toString proofFmt)
          | _ => pure "No proof term available"

        return {
          symbolName := name.toString,
          code := codeResult,
          completeLambdaTerm := completeLambdaTerm,
          proofTree := proofTree
        }
      | none =>
        throwThe RequestError ⟨.invalidParams,
          "No symbol found at cursor position. Move cursor to a theorem or definition."⟩


-- 1. Definisci il widget module con supporto RPC per leggere il tipo
@[widget_module]
def newWidget : Widget.Module where
    javascript := "" -- IGNORE: placeholder for the actual JavaScript code
--  javascript := include_str "cursorWidget.jsx"

-- 2. Registralo come panel widget sempre attivo
--    Da questo punto in poi il widget è visibile ovunque nel file.
show_panel_widgets [newWidget]


-- -------------------------------------------------------
-- Ora muovi il cursore qui sotto: il widget rimane visibile
-- e props.pos si aggiorna ad ogni spostamento.
-- -------------------------------------------------------

theorem esempio (n : Nat) : n + 0 = n := by
  -- sposta il cursore su queste righe tattiche:
  -- il widget è ancora lì, e mostra la riga corrente
  rfl

def unaFunzione (x : Nat) : Nat := x * 2

-- Teorema con più riscritture in sequenza
theorem addizione_riorganizzata (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]
-- Teorema con casi multipli usando match
theorem max_simmetrico (a b : Nat) : max a b = max b a := by
  cases Nat.lt_or_ge a b with
  | inl h =>
    -- Caso a < b
    rw [Nat.max_eq_right (Nat.le_of_lt h)]
    rw [Nat.max_eq_left]
    exact Nat.le_of_lt h
  | inr h =>
    -- Caso a ≥ b
    cases Nat.eq_or_lt_of_le h with
    | inl heq =>
      -- Sottocaso: a = b
      rw [heq]
    | inr hlt =>
      -- Sottocaso: a > b
      rw [Nat.max_eq_left h]
      rw [Nat.max_eq_right (Nat.le_of_lt hlt)]

-- Teorema con logica proposizionale (De Morgan)
theorem de_morgan (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · -- Dimostrazione andata: ¬(P ∨ Q) → (¬P ∧ ¬Q)
    intro h
    constructor
    · -- Dimostro ¬P
      intro hp
      apply h
      left
      exact hp
    · -- Dimostro ¬Q
      intro hq
      apply h
      right
      exact hq
  · -- Dimostrazione ritorno: (¬P ∧ ¬Q) → ¬(P ∨ Q)
    intro ⟨hnp, hnq⟩ hpq
    cases hpq with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

-- Teorema con esistenziali
theorem esiste_doppio (n : Nat) : ∃ m : Nat, m = 2 * n := by
  exists 2 * n

-- Teorema con induzione semplice
theorem zero_somma (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- Caso base: 0 + 0 = 0
    rfl
  | succ k ih =>
    -- Passo induttivo: 0 + (k+1) = k+1
    rw [Nat.add_succ]
    rw [ih]

-- Teorema con catene di implicazioni e passaggi multipli
theorem transitività_disuguaglianza (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  have h3 : a ≤ b := Nat.le_of_lt h1
  have h4 : b ≤ c := Nat.le_of_lt h2
  have h5 : a ≤ c := Nat.le_trans h3 h4
  have h6 : a ≠ c := by
    intro heq
    rw [heq] at h1
    exact Nat.lt_irrefl c (Nat.lt_trans h1 h2)
  exact Nat.lt_of_le_of_ne h5 h6

-- Teorema con calcoli espliciti
theorem quadrato_successore (n : Nat) : (n + 1) * (n + 1) = n * n + n + n + 1 := by
  calc (n + 1) * (n + 1)
    = (n + 1) * n + (n + 1) * 1 := by rw [Nat.mul_add]
  _ = (n * n + n) + (n + 1) := by simp [Nat.add_mul, Nat.one_mul, Nat.mul_one]
  _ = n * n + n + n + 1 := by omega

show_panel_widgets [- newWidget]
