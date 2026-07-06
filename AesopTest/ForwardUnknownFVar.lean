/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop

attribute [aesop safe forward 1] Nat.le_trans
attribute [-aesop] Aesop.BuiltinRules.applyHyps

variable (a b c d e f : Nat)

/-- error: Tactic `aesop` failed, failed to prove the goal after exhaustive search. -/
#guard_msgs in
set_option aesop.smallErrorMessages true in
example (h₃ : c ≤ d) (h₄ : d ≤ e) (h₅ : e ≤ f) (h : a = f) : False := by
  aesop (config := { terminal := true })
