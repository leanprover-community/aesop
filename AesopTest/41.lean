import Aesop

set_option aesop.check.all true

/--
error: no such rule set: 'Nonexistent'
  (Use 'declare_aesop_rule_set' to declare rule sets.
   Declared rule sets are not visible in the current file; they only become visible once you import the declaring file.)
-/
#guard_msgs in
example : True := by
  aesop (rule_sets := [Nonexistent])
