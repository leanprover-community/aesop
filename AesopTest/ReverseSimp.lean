/-
Copyright (c) 2026 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true
set_option linter.unusedVariables false

/-!
Tests for the `←` modifier on `simp` rules, which uses the rule in the
right-to-left direction, mirroring `simp [← h]`.
-/

-- A basic test: `←` reverses an iff, so `h : α ↔ β` rewrites `β` to `α`.
example {α β : Prop} (h : α ↔ β) (ha : α) : β := by
  aesop (rule_sets := [-builtin,-default]) (add simp [← h])

-- `←` combined with an explicit phase.
example {α β : Prop} (h : α ↔ β) (ha : α) : β := by
  aesop (rule_sets := [-builtin,-default]) (add norm simp [← h])

-- `←` on one rule among several.
example {α β δ γ : Prop} (h₁ : α → β) (h₂ : δ ↔ γ) (ha : α) (hd : δ) :
    β ∧ γ := by
  aesop (rule_sets := [-builtin,-default]) (add simp [h₁, ← h₂])

section LocalDirection

-- Direction-sensitive tests: `Pred`, `cA` and `cB` are opaque constants, so
-- the goal `Pred cB` can only be closed by `predCA : Pred cA` after the goal
-- has been rewritten right-to-left.

axiom Pred : Nat → Prop
axiom cA : Nat
axiom cB : Nat
axiom predCA : Pred cA

example (h : cA = cB) : Pred cB := by
  aesop (rule_sets := [-builtin,-default]) (add simp [← h], 90% apply predCA)

-- The forward direction does not close this goal, so the test above really
-- uses `h` right-to-left.
/--
error: Tactic `aesop` failed, made no progress
-/
#guard_msgs in
example (h : cA = cB) : Pred cB := by
  aesop (rule_sets := [-builtin,-default]) (add simp [h], 90% apply predCA)

end LocalDirection

section GlobalDirection

-- `←` also works with global theorems.

axiom RR : Prop → Prop
axiom pProp : Prop
axiom qProp : Prop
axiom rPQ : RR (pProp ∧ qProp)

theorem andCommIff : pProp ∧ qProp ↔ qProp ∧ pProp := And.comm

example : RR (qProp ∧ pProp) := by
  aesop (rule_sets := [-builtin,-default]) (add simp [← andCommIff], 90% apply rPQ)

-- The forward direction does not close this goal.
/--
error: Tactic `aesop` failed, made no progress
-/
#guard_msgs in
example : RR (qProp ∧ pProp) := by
  aesop (rule_sets := [-builtin,-default]) (add simp [andCommIff], 90% apply rPQ)

-- The `add_aesop_rules` command (which registers global rules in the default
-- rule set) supports `←` as well. Without the reversed rule, this goal is not
-- provable: `rPQ` does not apply to `RR (qProp ∧ pProp)` and the default simp
-- set does not contain `andCommIff`.
add_aesop_rules norm simp [← andCommIff]

example : RR (qProp ∧ pProp) := by
  aesop (rule_sets := [-builtin]) (add 90% apply rPQ)

end GlobalDirection

-- `←` is rejected for non-simp builders.
/--
error: aesop: ← is only supported for simp rules
-/
#guard_msgs in
example {α : Prop} (h : α) : α := by
  aesop (add safe apply [← h])
