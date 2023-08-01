/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.SearchM

open Lean

namespace Aesop

variable [Aesop.Queue Q]

def selectNormRules (rs : RuleSet) (goal : MVarId) :
    ProfileT MetaM (Array (IndexMatchResult NormRule)) :=
  profiling (rs.applicableNormalizationRules goal) λ _ elapsed =>
    recordRuleSelectionProfile elapsed

def preprocessRule : SafeRule where
  name := {
    name := `Aesop.BuiltinRule.preprocess
    builder := .tactic
    phase := .safe
    scope := .global
  }
  indexingMode := .unindexed
  extra := { penalty := 0, safety := .safe }
  tac := .preprocess

def selectSafeRulesCore (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) := do
  if ← g.isRoot then
    return #[{ rule := preprocessRule, locations := ∅ }]
  let ruleSet := (← read).ruleSet
  g.runMetaMInPostNormState' λ postNormGoal =>
    ruleSet.applicableSafeRules postNormGoal

def selectSafeRules (g : Goal) :
    SearchM Q (Array (IndexMatchResult SafeRule)) :=
  profiling (selectSafeRulesCore g) λ _ elapsed =>
    recordRuleSelectionProfile elapsed

def selectUnsafeRulesCore (postponedSafeRules : Array PostponedSafeRule)
    (gref : GoalRef) : SearchM Q UnsafeQueue := do
  let g ← gref.get
  match g.unsafeQueue? with
  | some rules => return rules
  | none => do
    let ruleSet := (← read).ruleSet
    let unsafeRules ←  g.runMetaMInPostNormState' λ postNormGoal =>
      ruleSet.applicableUnsafeRules postNormGoal
    let unsafeQueue := UnsafeQueue.initial postponedSafeRules unsafeRules
    gref.set $ g.setUnsafeRulesSelected true |>.setUnsafeQueue unsafeQueue
    return unsafeQueue

def selectUnsafeRules (postponedSafeRules : Array PostponedSafeRule)
    (gref : GoalRef) : SearchM Q UnsafeQueue :=
  profiling (selectUnsafeRulesCore postponedSafeRules gref) λ _ elapsed =>
    recordRuleSelectionProfile elapsed

end Aesop
