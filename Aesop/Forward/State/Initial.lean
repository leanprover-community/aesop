/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.RuleSet

open Lean Lean.Meta

namespace Aesop.LocalRuleSet

def mkInitialForwardState (goal : MVarId) (rs : LocalRuleSet) :
    MetaM (ForwardState × Array ForwardRuleMatch) :=
  goal.withContext do
    let mut fs := ∅
    let mut ruleMatches := #[]
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← rs.applicableForwardRules ldecl.type
      let (fs', ruleMatches') ←
        fs.addHypCore ruleMatches goal ldecl.fvarId rules
      fs := fs'
      ruleMatches := ruleMatches'
    return (fs, ruleMatches)


end Aesop.LocalRuleSet
