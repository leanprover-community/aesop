/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- Aesop `simp` substitutes `let` hypotheses even when `zetaDelta` is disabled
-- (which is the default).

/--
error: unsolved goals
P : Nat → Type
h : P 0
x : Nat := 0
⊢ P 0
-/
#guard_msgs in
example (P : Nat → Type) (h : P 0) : let x := 0; P x := by
  intro x
  aesop (rule_sets := [-builtin,-default])
    (config := { warnOnNonterminal := false })

/--
error: unsolved goals
P : Nat → Type
h : P 0
x : Nat := 0
⊢ P 0
-/
#guard_msgs in
example (P : Nat → Type) (h : P 0) : let x := 0; P x := by
  intro x
  aesop (rule_sets := [-builtin,-default])
    (config := { useSimpAll := false, warnOnNonterminal := false })
