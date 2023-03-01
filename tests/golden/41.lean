import Aesop

example : True := by
  aesop (rule_sets [Nonexistent])
