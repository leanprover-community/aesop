/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Lean
import Aesop

open Aesop.BuiltinRules.SplitHyps (splitHyps)
open Lean.Elab.Tactic

syntax (name := splitHyps) "splitHyps" : tactic

@[tactic splitHyps]
def evalSplitHyps : Tactic := λ _ => liftMetaTactic λ goal =>
  return [(← splitHyps goal).snd]

-- Note: the names of generated hypotheses are more or less arbitrary and should
-- not be relied upon.
set_option tactic.hygienic false

-- We can split product-like types.
example {P Q} (h : P ∧ Q) : Q ∧ P := by
  splitHyps
  exact ⟨h_2, h_1⟩

-- We can split product-like types under leading Π binders.
example {P Q : α → Prop} (h : ∀ x, P x ∧ Q x) (y) : Q y ∧ P y := by
  splitHyps
  exact ⟨h_2 y, h_1 y⟩

-- All product-like types from the standard library are supported (but not
-- arbitrary structures).
example {P : Type 1} {Q : Type 2} (h : P × Q) : PProd Q P := by
  splitHyps
  constructor; all_goals assumption

example {P : Prop} {Q : Type 1} (h : PProd P Q) : PProd Q P := by
  splitHyps
  constructor; all_goals assumption

example {P Q : Type 1} (h : MProd P Q) : Q × P := by
  splitHyps
  constructor; all_goals assumption

-- All sigma-like types from the standard library are supported.
example {X : Type} {P : X → Type} (h : Σ x, P x) : Σ x, P x := by
  splitHyps
  constructor; all_goals assumption

example {X : Prop} {P : X → Type 2} (h : Σ' x, P x) : Σ' x, P x := by
  splitHyps
  constructor; all_goals assumption

example {X : Type} {P : X → Prop} (h : ∃ x, P x) : ∃ x, P x := by
  splitHyps
  constructor; all_goals assumption

example {X Y : Type} {P : X → Y → Prop} (h : ∃ x, ∃ y, P x y) :
    ∃ x, ∃ y, P x y := by
  splitHyps
  splitHyps -- TODO splitHyps currently does not split the second ∃
  constructor; constructor; all_goals assumption

-- Sigma-like types can be split under Π binders as well, except for
-- Exists. (See note in the splitHyps code for why.) Also, splitting recurses
-- into nested products/existentials.
example {P : α → Type} {Q R : ∀ {a}, P a → Type}
    (h : ∀ a, Σ (y : P a), Q y × R y) (a) :
    Σ (y : P a), Q y × R y := by
  splitHyps
  exact ⟨h_1 a, h a, h_3 a⟩
