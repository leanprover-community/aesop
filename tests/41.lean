import Aesop

set_option aesop.check.all true

example : True := by
  aesop (rule_sets [Nonexistent])
