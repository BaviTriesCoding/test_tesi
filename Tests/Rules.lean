-- import Lean
import DeductionTreeWidget.DeductionTreeWidget
-- open Lean Meta Server Widget

-- =================
-- LOGICA
-- =================

macro "and_e" h:term:max ppSpace colGt l1:ident ppSpace colGt l2:ident : tactic =>
 `(tactic|refine And.casesOn $h (fun $l1 $l2 => ?_))

macro "or_e" h:term:max ppSpace colGt l1:ident ppSpace colGt l2:ident : tactic =>
 `(tactic|refine Or.casesOn $h (fun $l1 => ?_) (fun $l2 => ?_))

-- ══════════════════════════════════════════════════════════════════
-- ATTIVA I WIDGET
-- ══════════════════════════════════════════════════════════════════
show_panel_widgets [NDTreeJsonViewerWidget]

set_option pp.proofs true

theorem foo2 (A : Prop) (h : A) : A := by
  exact h

theorem ImplIntroElim {P Q R : Prop} (h: P -> Q) (p: R -> P) : R -> Q := by
 intro r
 apply h
 apply p
 exact r

theorem Andleft' (P Q : Prop) (h : P ∧ Q) : P := by
 exact And.casesOn h (fun p q => p)

theorem Andleft'' (P Q : Prop) (h : P ∧ Q) : P := by
 apply And.left h

theorem Andleft (P Q : Prop) (h : P ∧ Q) : P := by
 and_e h p _q
 exact p

theorem Andright'' (P Q : Prop) (h : P ∧ Q) : Q := by
 apply And.right h

theorem Andright (P Q : Prop) (h : P ∧ Q) : Q := by
  and_e h _p q
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
  or_e h1 p q
  . apply h2 p
  . apply h3 q

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
