/-
Copyright (c) 2024 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import Aesop.Forward.RuleInfo
import Aesop.Percent
import Aesop.Rule.Name
import Aesop.RuleTac.RuleTerm

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
  deriving Inhabited, BEq

namespace ForwardRulePriority

/-- If a `ForwardRulePriority` contains a penalty, extract it. -/
def penalty? : ForwardRulePriority → Option Int
  | .normSafe n => some n
  | .unsafe .. => none

/-- If a `ForwardRulePriority` contains a success probability, extract it. -/
def successProbability? : ForwardRulePriority → Option Percent
  | .unsafe p => some p
  | .normSafe .. => none

/-- Compare two rule priorities. Less means higher priority ('better').
Norm/safe rules have higher priority than unsafe rules. Among norm/safe rules,
lower penalty is better. Among unsafe rules, higher percentage is better. -/
protected def compare : (p₁ p₂ : ForwardRulePriority) → Ordering
  | .normSafe .., .unsafe .. => .lt
  | .unsafe .., .normSafe .. => .gt
  | .normSafe n₁, .normSafe n₂ => compare n₁ n₂
  | .unsafe p₁, .unsafe p₂ => compare p₁ p₂ |>.swap

instance : Ord ForwardRulePriority :=
  ⟨ForwardRulePriority.compare⟩

instance : ToString ForwardRulePriority where
  toString
    | .normSafe n => toString n
    | .unsafe p => p.toHumanString

end ForwardRulePriority

/-- A forward rule. -/
structure ForwardRule extends ForwardRuleInfo where
  /-- The rule's name. Should be unique among all rules in a rule set. -/
  name : RuleName
  /-- The theorem from which this rule is derived. -/
  term : RuleTerm
  /-- The rule's priority. -/
  prio : ForwardRulePriority
  deriving Inhabited

namespace ForwardRule

instance : BEq ForwardRule :=
  ⟨λ r₁ r₂ => r₁.name == r₂.name⟩

instance : Hashable ForwardRule :=
  ⟨λ r => hash r.name⟩

instance : Ord ForwardRule :=
  ⟨λ r₁ r₂ => compare r₁.prio r₂.prio |>.then (compare r₁.name r₂.name)⟩

instance : ToString ForwardRule where
  toString r := s!"[{r.prio}] {r.name}"

/-- Is this rule a `destruct` rule (i.e., should we clear matched hyps)? -/
def destruct (r : ForwardRule) : Bool :=
  r.name.builder matches .destruct

end Aesop.ForwardRule
