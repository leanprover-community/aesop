/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.SearchM

open Lean

namespace Aesop

variable [Aesop.Queue Q]

def selectSafeRules (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) := do
  let ruleSet := (← read).ruleSet
  g.runMetaMInPostNormState' λ postNormGoal =>
    ruleSet.applicableSafeRules postNormGoal

def selectUnsafeRules (postponedSafeRules : Array PostponedSafeRule)
    (gref : GoalRef) : SearchM Q UnsafeQueue := do
  let g ← gref.get
  match g.unsafeQueue? with
  | some rules => return rules
  | none => do
    let ruleSet := (← read).ruleSet
    let unsafeRules ←  g.runMetaMInPostNormState' λ postNormGoal =>
      ruleSet.applicableUnsafeRules postNormGoal
    let unsafeQueue := UnsafeQueue.initial postponedSafeRules unsafeRules
    aesop_trace[steps] "Selected unsafe rules:{MessageData.node $ unsafeQueue.entriesToMessageData}"
    gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
    return unsafeQueue

end Aesop
