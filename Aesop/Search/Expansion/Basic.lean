/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic
import Aesop.Tree.Data
import Aesop.Forward.State.ApplyGoalDiff

open Lean
open Lean.Meta

namespace Aesop

def runRuleTac (tac : RuleTac) (ruleName : RuleName)
    (preState : Meta.SavedState) (input : RuleTacInput) :
    BaseM (Except Exception RuleTacOutput) := do
  let result ←
    try
      Except.ok <$> runInMetaState preState do tac input
    catch e =>
      return .error e
  if ← Check.rules.isEnabled then
    if let .ok ruleOutput := result then
      ruleOutput.applications.forM λ rapp => do
        if let (some err) ← rapp.check input then
          throwError "{Check.rules.name}: while applying rule {ruleName}: {err}"
  return result

def GoalRef.progressForwardStateToPhase (phase : PhaseName) (rs : LocalRuleSet)
    (rootMetaState : Meta.SavedState) (gref : GoalRef) : BaseM Unit := do
  let (fs, ms) ← gref.modifyGet fun g =>
    ((g.forwardState, g.forwardRuleMatches),
     g.setForwardState default |>.setForwardRuleMatches default)
  let (_, metaState) ← (← gref.get).currentGoalAndMetaState rootMetaState
  let (fs, ms') ← runInMetaState metaState do fs.progressToPhase phase rs
  gref.modify fun g =>
    g.setForwardState fs |>.setForwardRuleMatches (ms.insertMany ms')

end Aesop
