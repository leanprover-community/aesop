import Aesop

open Aesop

set_option aesop.check.all true

inductive Even : Nat → Prop
| zero : Even 0
| plusTwo : Even n → Even (n + 2)

attribute [aesop safe] Even.zero

def limitedEvenPlusTwo : RuleTac :=
  RuleTac.withApplicationLimit 2 $ RuleTac.applyConst ``Even.plusTwo

example : Even 4 := by
  aesop (add safe limitedEvenPlusTwo)

example : Even 6 := by
  fail_if_success aesop (add safe limitedEvenPlusTwo)
  aesop (add safe (tactic (uses_branch_state := false)) limitedEvenPlusTwo)
