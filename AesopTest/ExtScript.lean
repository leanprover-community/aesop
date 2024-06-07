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
  ext1
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
  ext1
  · sorry
  · ext1
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
  ext1
  · ext1 x
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
  ext1
  · ext1 x
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
