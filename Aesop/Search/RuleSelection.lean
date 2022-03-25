/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.SearchM

open Lean

namespace Aesop

variable [Aesop.Queue Q]

def SafeRule.asUnsafeRule (r : SafeRule) : UnsafeRule :=
  { r with extra := { successProbability := Percent.ninety } }

def selectSafeRules (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) := do
  let ruleSet := (← read).ruleSet
  g.runMetaMInPostNormState' λ postNormGoal =>
    ruleSet.applicableSafeRules postNormGoal

def selectUnsafeRules (gref : GoalRef) (includeSafeRules : Bool) :
    SearchM Q UnsafeQueue := do
  let g ← gref.get
  match g.unsafeQueue? with
  | some rules => return rules
  | none => do
    let ruleSet := (← read).ruleSet
    let unsafeRules ← g.runMetaMInPostNormState' λ postNormGoal =>
      ruleSet.applicableUnsafeRules postNormGoal
    let rules ←
      if includeSafeRules then
          let safeRules ← selectSafeRules g
          let rules :=
            safeRules.map (λ r => { r with rule := r.rule.asUnsafeRule })
              |>.mergeSortedPreservingDuplicates unsafeRules
              -- TODO why do we preserve duplicates here?
          aesop_trace[steps] "Selected unsafe rules (including safe rules treated as unsafe):{MessageData.node $ rules.map toMessageData}"
          pure rules
      else
        aesop_trace[steps] "Selected unsafe rules:{MessageData.node $ unsafeRules.map toMessageData}"
        pure unsafeRules
    let unsafeQueue := UnsafeQueue.initial rules
    gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
    return unsafeQueue

end Aesop
