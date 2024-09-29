/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Percent
import Aesop.Rule.Name
import Aesop.Forward.RuleInfo

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- The priority of a forward rule. -/
inductive ForwardRulePriority : Type where
  /-- If the rule is a norm or safe rule, its priority is an integer. -/
  | normSafe (n : Int) : ForwardRulePriority
  /-- If the rule is an unsafe rule, its priority is a percentage representing
  the rule's success probability. -/
  | «unsafe» (p : Percent) : ForwardRulePriority
  deriving Inhabited

/-- A forward rule. -/
structure ForwardRule extends ForwardRuleInfo where
  /-- The rule's name. Should be unique among all rules in a rule set. -/
  name : RuleName
  /-- The theorem from which this rule is derived. -/
  -- FIXME What happens if this expr becomes invalid due to fvar renamings etc.?
  expr : Expr
  /-- The rule's priority. -/
  prio : ForwardRulePriority
  deriving Inhabited

namespace ForwardRule

instance : BEq ForwardRule :=
  ⟨λ r₁ r₂ => r₁.name == r₂.name⟩

instance : Hashable ForwardRule :=
  ⟨λ r => hash r.name⟩

instance : Ord ForwardRule :=
  ⟨λ r₁ r₂ => compare r₁.name r₂.name⟩


end Aesop.ForwardRule
