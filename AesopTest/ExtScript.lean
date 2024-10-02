/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[ext]
structure MyProd (α β : Type _) where
  fst : α
  snd : β

variable {α β γ δ ι: Type}

/--
info: Try this:
  ext : 1
  · sorry
  · sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {p q : MyProd α β} : p = q := by
  aesop? (add safe Aesop.BuiltinRules.ext)
    (config := { warnOnNonterminal := false })
  all_goals sorry

/--
info: Try this:
  ext : 1
  · sorry
  · ext : 1
    · sorry
    · sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {p q : MyProd α (MyProd β γ)} : p = q := by
  aesop? (add safe Aesop.BuiltinRules.ext)
    (config := { warnOnNonterminal := false })
  all_goals sorry

/--
info: Try this:
  ext : 1
  · ext x : 1
    sorry
  · sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {p q : MyProd (α → β) γ} : p = q := by
  aesop? (add safe Aesop.BuiltinRules.ext)
    (config := { warnOnNonterminal := false })
  all_goals sorry

/--
info: Try this:
  ext : 1
  · ext x : 1
    sorry
  · ext x x_1 : 2
    sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {p q : (α → β) × (γ → δ → ι)} : p = q := by
  aesop? (add safe Aesop.BuiltinRules.ext)
    (erase Aesop.BuiltinRules.destructProducts)
    (config := { warnOnNonterminal := false })
  all_goals sorry

-- This test case checks script generation for ext calls which generate subgoals
-- with different numbers of new hypotheses.

axiom T : Type
axiom U : Type
axiom u : U
axiom v : U

@[ext (iff := false)]
axiom T_ext : ∀ x y : T, u = v → (∀ u v : U, u = v) → x = y

/--
info: Try this:
  ext u v : 1
  · sorry
  · sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (x y : T) : x = y := by
  aesop? (add safe Aesop.BuiltinRules.ext)
    (config := { warnOnNonterminal := false })
  all_goals sorry
