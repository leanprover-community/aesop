/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

open Lean Lean.Meta

namespace Aesop.LocalRuleSet

variable [Monad m] [MonadRulePatternCache m] [MonadAlwaysExcept Exception m]
  [MonadRPINF m]

def mkInitialForwardState (goal : MVarId) (rs : LocalRuleSet) :
    m (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    let mut fs : ForwardState := ∅
    let mut ruleMatches := rs.constForwardRuleMatches
    show MetaM _ from do
      aesop_trace[forward] do
        for m in ruleMatches do
          aesop_trace![forward] "match for constant rule {m.rule.name}"
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← rs.applicableForwardRules ldecl.type
      let patInsts ← rs.forwardRulePatternInstantiationsInLocalDecl ldecl
      let (fs', ruleMatches') ←
        fs.addHypWithPatInstsCore ruleMatches goal ldecl.fvarId rules patInsts
      fs := fs'
      ruleMatches := ruleMatches'
    let patInsts ← rs.forwardRulePatternInstantiationsInExpr (← goal.getType)
    fs.addPatInstsCore ruleMatches goal patInsts

end Aesop.LocalRuleSet
