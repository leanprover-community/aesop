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
-/
structure Options where
  maxRuleApplicationDepth := 30
  maxRuleApplications := 200
  maxGoals := 0
  deriving Inhabited, BEq, Repr

unsafe def evalOptionsExprImpl (e : Expr) : TermElabM Aesop.Options := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then throwError
    "error while evaluating expression '{e}': it may not contain metavariables or local hypotheses"
  check e
  let t ← inferType e
  let (true) ← isDefEq t (mkConst ``Aesop.Options) | throwError
    "expected '{e}' to have type{indentD "Aesop.Options"}\nbut it has type{indentExpr t}"
  evalExpr Aesop.Options ``Aesop.Options e

@[implementedBy evalOptionsExprImpl]
constant evalOptionsExpr (e : Expr) : TermElabM Aesop.Options

end Aesop
