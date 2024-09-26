/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Percent
import Aesop.Rule.Name
import Aesop.Forward.RuleInfo

open Lean Lean.Meta

namespace Aesop

/--
The priority of a forward rule.
-/
inductive ForwardRulePriority : Type where
  | normSafe (n : Int) : ForwardRulePriority
  | «unsafe» (p : Percent) : ForwardRulePriority
  deriving Inhabited

structure ForwardRule extends ForwardRuleInfo where
  name : RuleName
  expr : Expr
  prio : ForwardRulePriority
  deriving Nonempty

namespace ForwardRule

instance : BEq ForwardRule :=
  ⟨λ r₁ r₂ => r₁.name == r₂.name⟩

instance : Hashable ForwardRule :=
  ⟨λ r => hash r.name⟩

instance : Ord ForwardRule :=
  ⟨λ r₁ r₂ => compare r₁.name r₂.name⟩


end Aesop.ForwardRule
