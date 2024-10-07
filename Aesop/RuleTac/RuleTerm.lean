import Aesop.Rule.Name

open Lean Lean.Meta

namespace Aesop

inductive RuleTerm
  | const (decl : Name)
  | term (term : Term)
  deriving Inhabited

instance : ToMessageData RuleTerm where
  toMessageData
    | .const decl => m!"{decl}"
    | .term tm => m!"{tm}"

inductive ElabRuleTerm
  | const (decl : Name)
  | term (term : Term) (expr : Expr)
  deriving Inhabited

namespace ElabRuleTerm

instance : ToMessageData ElabRuleTerm where
  toMessageData
    | .const decl => m!"{decl}"
    | .term tm _ => m!"{tm}"

def expr : ElabRuleTerm → MetaM Expr
  | const decl => mkConstWithFreshMVarLevels decl
  | term _ e => return e

def scope : ElabRuleTerm → ScopeName
  | const .. => .global
  | term .. => .local

def name : ElabRuleTerm → MetaM Name
  | const decl => return decl
  | term _ e => getRuleNameForExpr e

def toRuleTerm : ElabRuleTerm → RuleTerm
  | const decl => .const decl
  | term t _ => .term t

def ofElaboratedTerm (tm : Term) (expr : Expr) : ElabRuleTerm :=
  if let some decl := expr.constName? then
    .const decl
  else
    .term tm expr

end Aesop.ElabRuleTerm
