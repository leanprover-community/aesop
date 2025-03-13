/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop

def runRuleTac (tac : RuleTac) (ruleName : RuleName)
    (preState : Meta.SavedState) (input : RuleTacInput) :
    BaseM (Sum Exception RuleTacOutput) := do
  let result ←
    tryCatchRuntimeEx
      (Sum.inr <$> runInMetaState preState do
        withAtMostMaxHeartbeats input.options.maxRuleHeartbeats do
          tac input)
      (λ e => return Sum.inl e)
  if ← Check.rules.isEnabled then
    if let (Sum.inr ruleOutput) := result then
      ruleOutput.applications.forM λ rapp => do
        if let (some err) ← rapp.check input then
          throwError "{Check.rules.name}: while applying rule {ruleName}: {err}"
  return result

end Aesop
