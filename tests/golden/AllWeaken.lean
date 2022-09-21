/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop

set_option aesop.check.all true

inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more {x xs} : P x → All P xs → All P (x :: xs)

@[aesop unsafe]
axiom weaken {α} (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α)
  (h : All P xs) : All Q xs

example : All (· ∈ []) (@List.nil α) := by
  aesop (options := { maxRuleApplications := 50, terminal := true })
