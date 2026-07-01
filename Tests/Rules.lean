-- import Lean
import DeductionTreeWidget.DeductionTreeWidget
-- open Lean Meta Server Widget

-- =================
-- LOGICA
-- =================

macro "or_e" h:term:max ppSpace colGt l1:ident ppSpace colGt l2:ident : tactic =>
 `(tactic|refine Or.casesOn $h (fun $l1 => ?_) (fun $l2 => ?_))

macro "and_e" h:term:max ppSpace colGt l1:ident ppSpace colGt l2:ident : tactic =>
 `(tactic|refine And.casesOn $h (fun $l1 $l2 => ?_))

macro "exists_e" h:term:max ppSpace colGt l1:ident ppSpace colGt l2:ident : tactic =>
 `(tactic|refine Exists.casesOn $h (fun $l1 $l2 => ?_))

-- ══════════════════════════════════════════════════════════════════
-- ATTIVA I WIDGET
-- ══════════════════════════════════════════════════════════════════
show_panel_widgets [NDTreeJsonViewerWidget]

set_option pp.proofs true

theorem foo2 (A C : Prop) (h : A ∧ C) : A ∧ C := by
  exact h

theorem ImplIntroElim {A P Q R : Prop} (h: P -> Q) (p: A → R → P) (a : A) : R -> Q := by
 intro r
 apply h (p a r)

theorem impmul (P Q R: Prop) (h: P → Q → R) : P → Q → R := by
  intro p q
  apply h p q

theorem impmul' (A P Q R: Prop) (h: A → P → Q → R) : A → P → Q → R := by
  intro a p q
  apply h a p q

theorem Andleft (P Q : Prop) (h : P ∧ Q) : P := by
 apply And.left h

theorem Andleft1 (P Q : Prop) (h : P ∧ Q) : P := by
 apply h.1

theorem Andright (P Q : Prop) (h : P ∧ Q) : Q := by
 apply And.right h

theorem AndElim (P Q : Prop) (h: P ∧ Q) : Q ∧ P := by
 and_e h p q
 constructor <;> assumption

theorem AndIntro (P Q : Prop) (h1 : P) (h2 : Q) : P ∧ Q := by
  apply And.intro
  . exact h1
  . exact h2

theorem AndCases (A B : Prop) (h: A ∧ B) : B ∧ A := by
  exact And.casesOn h
    fun ha hb => And.intro hb ha

theorem OrIntroLeft2 (P Q : Prop) (h : P) : P -> (P ∧ P ∨ Q) ∨ Q := by
  intro x
  apply Or.inl
  apply Or.inl
  apply And.intro x h

theorem OrIntroLeft (P Q : Prop) (h : P) : P ∨ Q := by
  apply Or.inl h

theorem OrIntroRight (P Q: Prop) (h : Q)  : P ∨ Q := by
  apply Or.inr h

theorem or_comm' (h : A ∨ B) : B ∨ A := by
  exact Or.casesOn h
    (fun ha => Or.inr ha)   -- caso A: costruiamo B ∨ A con inr
    (fun hb => Or.inl hb)   -- caso B: costruiamo B ∨ A con inl

theorem OrElim''  (h1: (A ∧ B) ∨ C) (h2: A → C) : C := by
  or_e h1 ab c
  . apply h2 (And.left ab)
  . exact c

theorem NotIntro (P : Prop) (h : ¬P): ¬P := by
  intro h2
  apply h h2

theorem NotIntro' (P : Prop) (h : ¬P) : P → False := by
  intro p
  apply h p

theorem NotIntro'' (A P : Prop) (h : ¬P) : A → ¬P := by
  intro a
  intro p
  apply h p

theorem NotElim (P : Prop) (h1 : ¬P) (h2 : P) : False := by
  apply h1 h2

theorem NotElim' (P : Prop) (h1 : ¬P) (h2 : P) : False := by
  apply absurd h2 h1

theorem foo (A B C D : Prop) (h1: (A ∧ B) ∧ (C ∧ D)) : A ∧ C := by
  have h2 : A ∧ B := And.left h1
  have a : A := And.left h2
  have h1 : C := And.left (And.right h1)
  exact And.intro a h1

theorem lal (A B : Prop) (a: A) (b : B) : A ↔ B := by
  apply Iff.intro
  . intro
    exact b
  . intro
    exact a

theorem andAnd (A B C : Prop) (h : A ∧ (B ∧ C)) : C := by
  have h1 : B ∧ C := And.right h
  have c : C := And.right h1
  exact c

theorem forallTest : ∀(A: Prop), A ↔ A := by
  intro A
  apply Iff.intro
  . intro a
    exact a
  . intro a'
    exact a'

theorem iffTest (A B: Prop) (h: A ↔ B) : B → A := by
  exact h.mpr

theorem iffTest' (A B: Prop) (h: A ↔ B) : A → B := by
  exact h.mp

theorem IffTest'' (A B: Prop) (h : A ↔ B) : B ↔ A := by
  exact h.symm

theorem ExIntroElim (A : Type) (P : A -> Prop) (H: ∃x, P x) : ∃y, P y := by
  exists_e H d hyp
  apply Exists.intro d
  -- CSC: bug here
  assumption

theorem topIntro : True := by
  apply True.intro

theorem topElim (H: True) : True := by
  cases H
  apply True.intro
  -- CSC: bugs here

theorem falseElim {A: Prop} (H: False) : A := by
  cases H
  -- CSC: bugs here

show_panel_widgets [- NDTreeJsonViewerWidget]
