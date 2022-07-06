import Lean

open Lean
open Lean.Meta
open Lean.Elab.Term

namespace Aesop

/--
Options that modify Aesop's behaviour. Available options are:

- `maxRuleApplicationDepth`: maximum number of rule applications in any branch
  of the search tree, aka maximum search depth. When a branch exceeds this
  limit, it is considered unprovable; other branches may still be explored. 0
  means no limit.
- `maxRuleApplications`: maximum number of rule applications in the search tree.
  When this limit is exceeded, the search ends. 0 means no limit.
- `maxGoals`: maximum number of goals in the search tree. When this limit is
  exceeded, the search ends. 0 means no limit.
- `maxNormIterations`: maximum number of norm rules applied to a *single* goal.
  When this limit is exceeded, normalisation is likely stuck in an infinite loop
  so Aesop fails. 0 means no limit.
- `terminal`: if `true`, Aesop succeeds only if it proves the goal. If `false`,
  Aesop always succeeds and reports the goals remaining after safe rules were
  applied.
- `warnOnNonterminal`: print a warning when Aesop does not prove the goal.
-/
structure Options where
  maxRuleApplicationDepth := 30
  maxRuleApplications := 200
  maxGoals := 0
  maxNormIterations := 100
  terminal := false
  warnOnNonterminal := true
  deriving Inhabited, BEq, Repr

end Aesop
