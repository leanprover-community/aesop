import Aesop.RuleTac.Basic
import Aesop.Forward.Match.Types

open Lean Lean.Meta

namespace Aesop

inductive RuleTacDescr
  | apply (term : RuleTerm) (md : TransparencyMode)
  | constructors (constructorNames : Array Name) (md : TransparencyMode)
  | forward (term : RuleTerm) (immediate : UnorderedArraySet PremiseIndex)
      (isDestruct : Bool)
  | cases (target : CasesTarget) (md : TransparencyMode)
      (isRecursiveType : Bool) (ctorNames : Array CtorNames)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | tacGen (decl : Name)
  | singleRuleTac (decl : Name)
  | tacticStx (stx : Syntax)
  | preprocess
  | forwardMatch (m : ForwardRuleMatch)
  deriving Inhabited

namespace RuleTacDescr

def forwardRuleMatch? : RuleTacDescr → Option ForwardRuleMatch
  | forwardMatch m => m
  | _ => none

end RuleTacDescr

end Aesop
