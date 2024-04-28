/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

@[aesop 50%]
inductive Even : Nat → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

structure Even' (n) : Prop where
  even : Even n

theorem even'_of_false : False → Even' n
| h => nomatch h

theorem even'_of_even' : Even' n → Even' n :=
  id

-- Once a safe rule is applied, the corresponding goal is marked as inactive
-- and never visited again.

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Even' 2 := by
  aesop (add safe [even'_of_false 0, Even'.mk 1])
    (config := { terminal := true })

/--
error: tactic 'aesop' failed, maximum number of rule applications (10) reached. Set the 'maxRuleApplications' option to increase the limit.
-/
#guard_msgs in
example : Even' 2 := by
  aesop (add safe [even'_of_even'], unsafe [Even'.mk 100%])
    (config := { maxRuleApplications := 10, terminal := true })

example : Even' 2 := by
  aesop (add safe [even'_of_false 1, Even'.mk 0])
