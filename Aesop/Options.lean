import Lean

open Lean
open Lean.Meta
open Lean.Elab.Term

namespace Aesop

structure Options where
  maxRuleApplicationDepth := 30 -- 0 means no limit
  maxRuleApplications := 200    -- 0 means no limit
  maxGoals := 0                 -- 0 means no limit
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
