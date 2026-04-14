import Lean
open Lean Meta

abbrev Var := String

#check ppExpr
#check Widget.CodeWithInfos -- generato con Widget.ppExprTagged

/-
inductive Formula  where
  | pred   : Widget.CodeWithInfos → Formula
  | top    : Formula                     -- ⊤ ▸ Formula
  | bottom : Formula                     -- ⊥ ▸ Formula
  | and    : Formula → Formula → Formula -- A ∧ B ▸ ⟨Formula, Formula⟩ → Formula
  | or     : Formula → Formula → Formula -- A ∨ B ▸ ⟨Formula, Formula⟩ → Formula
  | not    : Formula → Formula           -- ¬A → Formula → Formula
  | imp    : Formula → Formula → Formula -- ⟨Formula, Formula⟩ → Formula
  | forAll : Var → Formula → Formula     -- ∀x. Formula ▸ ⟨Var, Formula⟩ → Formula
  | exists : Var → Formula → Formula     -- ∃x. Formula ▸ ⟨Var, Formula⟩ → Formula
-/

abbrev Formula := Widget.CodeWithInfos
abbrev Proof := Widget.CodeWithInfos

inductive NDTree where
  | leaf : Formula → Bool → NDTree
  | node : List NDTree → Formula → String → NDTree
  | unhandled : Proof → Formula → NDTree

-- usare NDTree come struttura dati per rappresentare gli alberi
-- mkFreshFVarId : MetaM FVarId che ci permette di avere le variabili per rappresentare le ipotesi
-- instantiate1 : Expr → FVarId → Expr che ci permette di sostituire le variabili nelle formule
