/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Tree.RunMetaM
import Aesop.Search.SearchM

open Lean

namespace Aesop

variable [Aesop.Queue Q]

def selectNormRules (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) : BaseM (Array (IndexMatchResult NormRule)) :=
  profilingRuleSelection do rs.applicableNormalizationRules fms goal

def preprocessRule : SafeRule where
  name := {
    name := `Aesop.BuiltinRule.preprocess
    builder := .tactic
    phase := .safe
    scope := .global
  }
  indexingMode := .unindexed
  pattern? := none
  extra := { penalty := 0, safety := .safe }
  tac := .preprocess

def selectSafeRules (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) := do
  profilingRuleSelection do
    if ← g.isRoot then
      return #[{
        rule := preprocessRule
        locations := ∅
        patternSubsts? := none
      }]
    let ruleSet := (← read).ruleSet
    g.runMetaMInPostNormState' λ postNormGoal =>
      ruleSet.applicableSafeRules g.forwardRuleMatches postNormGoal

def selectUnsafeRules (postponedSafeRules : Array PostponedSafeRule)
    (gref : GoalRef) : SearchM Q UnsafeQueue := do
  profilingRuleSelection do
    let g ← gref.get
    match g.unsafeQueue? with
    | some rules => return rules
    | none => do
      let ruleSet := (← read).ruleSet
      let unsafeRules ←
        g.runMetaMInPostNormState' λ postNormGoal =>
          ruleSet.applicableUnsafeRules g.forwardRuleMatches postNormGoal
      let unsafeQueue := UnsafeQueue.initial postponedSafeRules unsafeRules
      gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
      return unsafeQueue

end Aesop
