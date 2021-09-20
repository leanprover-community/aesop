import Aesop

open Aesop

inductive Even : Nat → Prop
| zero : Even 0
| plusTwo : Even n → Even (n + 2)

attribute [aesop safe] Even.zero

@[aesop safe]
def limitedEvenPlusTwo : RuleTac :=
  RuleTac.withApplicationLimit 2 $ RuleTac.applyConst ``Even.plusTwo

example : Even 4 := by
  aesop

example : Even 6 := by
  failIfSuccess aesop
  exact Even.plusTwo $ Even.plusTwo $ Even.plusTwo Even.zero
