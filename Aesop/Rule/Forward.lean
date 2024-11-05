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

/-- Compare two rule priorities. Norm/safe rules have higher priority than
unsafe rules. Among norm/safe rules, lower penalty is better (lower). Among
unsafe rules, higher percentage is better. -/
protected def le : (p₁ p₂ : ForwardRulePriority) → Bool
  | .normSafe _, .unsafe _ => true
  | .unsafe _, .normSafe _ => true
  | .normSafe n₁, .normSafe n₂ => n₁ ≤ n₂
  | .unsafe p₁, .unsafe p₂ => p₁ ≥ p₂

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
  ⟨λ r₁ r₂ => compare r₁.name r₂.name⟩

instance : ToString ForwardRule where
  toString r := s!"[{r.prio}] {r.name}"

/-- The number of premise indexes used by the rule. Data structures related to
the rule use only premise indexes in the interval `[0, numPremiseIndexes)`. -/
def numPremiseIndexes (r : ForwardRule) : Nat :=
  if r.rulePatternInfo?.isSome then
    r.numPremises + 1
  else
    r.numPremises

/-- Is this rule a `destruct` rule (i.e., should we clear matched hyps)? -/
def destruct (r : ForwardRule) : Bool :=
  r.name.builder matches .destruct

end Aesop.ForwardRule
