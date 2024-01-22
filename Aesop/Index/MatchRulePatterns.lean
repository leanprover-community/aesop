/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic

open Lean Lean.Meta

namespace Aesop

section

variable {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m]
    [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]

def forEachExprInGoalCore (mvarId : MVarId) (g : Expr → m Bool) :
    MonadCacheT Expr Unit m Unit :=
  mvarId.withContext do
    for ldecl in ← show MetaM _ from getLCtx do
      ForEachExpr.visit g ldecl.type
      if let some value := ldecl.value? then
        ForEachExpr.visit g value
    ForEachExpr.visit g (← mvarId.getType)

@[inline, always_inline]
def forEachExprInGoal' (mvarId : MVarId) (g : Expr → m Bool) : m Unit :=
  forEachExprInGoalCore mvarId g |>.run

@[inline, always_inline]
def forEachExprInGoal (mvarId : MVarId) (g : Expr → m Unit) : m Unit :=
  forEachExprInGoal' mvarId λ e => do g e; return true

end

def matchRulePatternsCore (pats : Array (RuleName × RulePattern))
    (mvarId : MVarId) :
    StateRefT (HashMap RuleName (HashSet RulePatternInstantiation)) MetaM Unit :=
  withNewMCtxDepth do -- TODO use (allowLevelAssignments := true)?
    let openPats ← pats.mapM λ (name, pat) => return (name, ← pat.open)
    let initialState ← show MetaM _ from saveState
    forEachExprInGoal mvarId λ e => do
      for (name, mvarIds, p) in openPats do
        initialState.restore
        if ← isDefEq e p then
          let instances ← mvarIds.mapM λ mvarId => do
            let result ← instantiateMVars (.mvar mvarId)
            if result.isMVar then
              throwError "matchRulePatterns: expected {mvarId.name} to be assigned"
            pure result
          modify λ m =>
            -- TODO loss of linearity?
            if let some instanceSet := m.find? name then
              m.insert name (instanceSet.insert instances)
            else
              m.insert name (.empty |>.insert instances)

def matchRulePatterns (pats : Array (RuleName × RulePattern))
    (mvarId : MVarId) :
    MetaM (HashMap RuleName (HashSet RulePatternInstantiation)) :=
  return (← matchRulePatternsCore pats mvarId |>.run ∅).snd

end Aesop
