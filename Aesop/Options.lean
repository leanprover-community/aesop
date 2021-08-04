import Lean

open Lean
open Lean.Meta
open Lean.Elab.Term

namespace Aesop

structure Options where
  maxDepth := 1000
  maxRuleApplications := 10000
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
