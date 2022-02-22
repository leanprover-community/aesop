import Aesop.Main

inductive Even : Nat → Prop
| zero : Even Nat.zero
| plus_two {n} : Even n → Even (n + 2)

attribute [aesop safe] Even.zero Even.plus_two

example : Even 1000 := by
  aesop (options := { maxRuleApplications := 0, maxRuleApplicationDepth := 0 })
