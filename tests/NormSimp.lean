/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- A basic test for local simp rules.
example {α : Prop} (h : α) : α := by
  aesop (rule_sets [-builtin,-default]) (add h norm simp)

-- This test checks that we don't 'self-simplify' hypotheses: `h` should not
-- be used to simplify itself.
example (h : (α ∧ β) ∨ γ) : α ∨ γ := by
  aesop (add h norm simp)

-- This test checks that the norm fixpoint loop is correctly reset when norm
-- simp changes the goal.
declare_aesop_rule_sets [fixpoint]

inductive Void

@[aesop norm unfold (rule_sets [fixpoint])]
def T := False → Void

attribute [aesop norm -100 (rule_sets [fixpoint])] Aesop.BuiltinRules.intros

example : T := by
  aesop (rule_sets [-default,-builtin,fixpoint])
