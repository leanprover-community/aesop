/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.Match.Types
import Aesop.Index.Basic
import Aesop.Percent
import Aesop.Rule.Forward
import Aesop.RuleTac.GoalDiff
import Aesop.RuleTac.FVarIdSubst
import Aesop.Script.CtorNames
import Aesop.Script.Step
import Batteries.Lean.Meta.SavedState
import Aesop.Options.Internal

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop

/-! # Rule Tactic Types -/

-- TODO put docs on the structure fields instead of the structures

/--
Input for a rule tactic. Contains:

- `goal`: the goal on which the rule is run.
- `mvars`: the set of mvars which occur in `goal`.
- `indexMatchLocations`: if the rule is indexed, the locations (e.g. hyps or the
  target) matched by the rule's index entries. Otherwise an empty set.
- `patternInstantiations`: if the rule has a pattern, the pattern instantiations
  that were found in the goal. Each instantiation is a list of expressions which
  were found by matching the pattern against expressions in the goal. For
  example, if `h : max a b = max a c` appears in the goal and the rule has
  pattern `max x y`, there will be two pattern instantiations `[a, b]`
  (representing the substitution `{x ↦ a, y ↦ b}`) and `[a, c]`. If the rule
  does not have a pattern, `patternInstantiations` is empty; otherwise it's
  guaranteed to be non-empty.
- `options`: the options given to Aesop.
-/
structure RuleTacInput where
  goal : MVarId
  mvars : UnorderedArraySet MVarId
  indexMatchLocations : Std.HashSet IndexMatchLocation
  patternInstantiations : Std.HashSet RulePatternInstantiation
  options : Options'
  deriving Inhabited

/-- A subgoal produced by a rule. -/
structure Subgoal where
  /--
  A diff between the goal the rule was run on and this goal. Many `MetaM`
  tactics report information that allows you to easily construct a `GoalDiff`.
  If you don't have access to such information, use `diffGoals`, but note that
  it may not give optimal results.
  -/
  diff : GoalDiff
  deriving Inhabited

namespace Subgoal

def mvarId (g : Subgoal) : MVarId :=
  g.diff.newGoal

end Subgoal

def mvarIdToSubgoal (parentMVarId mvarId : MVarId) (fvarSubst : FVarIdSubst) :
    MetaM Subgoal :=
  return { diff := ← diffGoals parentMVarId mvarId fvarSubst }

/--
A single rule application, representing the application of a tactic to the input
goal. Must accurately report the following information:

- `goals`: the goals generated by the tactic.
- `postState`: the `MetaM` state after the tactic was run.
- `scriptSteps?`: script steps which produce the same effect as the rule tactic.
  If `input.options.generateScript = false` (where `input` is the
  `RuleTacInput`), this field is ignored. If the tactic does not support script
  generation, use `none`.
- `successProbability`: The success probability of this rule application. If
  `none`, we use the success probability of the applied rule.
-/
structure RuleApplication where
  goals : Array Subgoal
  postState : Meta.SavedState
  scriptSteps? : Option (Array Script.LazyStep)
  successProbability? : Option Percent

namespace RuleApplication

def check (r : RuleApplication) (input : RuleTacInput) :
    MetaM (Option MessageData) :=
  r.postState.runMetaM' do
    for goal in r.goals do
      if ← goal.mvarId.isAssignedOrDelayedAssigned then
        return some m!"subgoal metavariable ?{goal.mvarId.name} is already assigned."
      if let some err ← goal.diff.check input.goal goal.mvarId then
        return some err
    return none

end RuleApplication

/--
The result of a rule tactic is a list of rule applications.
-/
structure RuleTacOutput where
  applications : Array RuleApplication
  deriving Inhabited

/--
A `RuleTac` is the tactic that is run when a rule is applied to a goal.
-/
def RuleTac := RuleTacInput → MetaM RuleTacOutput

instance : Inhabited RuleTac := by
  unfold RuleTac; exact inferInstance

/--
A `RuleTac` which generates only a single `RuleApplication`.
-/
def SingleRuleTac :=
  RuleTacInput →
  MetaM (Array Subgoal × Option (Array Script.LazyStep) × Option Percent)

@[inline]
def SingleRuleTac.toRuleTac (t : SingleRuleTac) : RuleTac := λ input => do
  let (goals, scriptSteps?, successProbability?) ← t input
  let postState ← saveState
  return ⟨#[{ postState, goals, scriptSteps?, successProbability? }]⟩

@[inline]
def RuleTac.ofSingleRuleTac := SingleRuleTac.toRuleTac

def RuleTac.ofTacticSyntax (t : RuleTacInput → MetaM Syntax.Tactic) : RuleTac :=
  RuleTac.ofSingleRuleTac λ input => do
    let stx ← t input
    let preState ← saveState
    let postGoals ← Lean.Elab.Tactic.run input.goal (evalTactic stx) |>.run'
    let postState ← saveState
    let postGoals := postGoals.toArray
    let step := {
      preGoal := input.goal
      tacticBuilders := #[return .unstructured stx]
      preState, postState, postGoals
    }
    let postGoals ← postGoals.mapM (mvarIdToSubgoal input.goal · ∅)
    return (postGoals, some #[step], none)

/--
A tactic generator is a special sort of rule tactic, intended for use with
generative machine learning methods. It generates zero or more tactics
(represented as strings) that could be applied to the goal, plus a success
probability for each tactic. When Aesop executes a tactic generator, it executes
each of the tactics and, if the tactic succeeds, adds a rule application for it.
The tactic's success probability (which must be between 0 and 1, inclusive)
becomes the success probability of the rule application. A `TacGen` rule
succeeds if at least one of its suggested tactics succeeds.
-/
abbrev TacGen := MVarId → MetaM (Array (String × Float))

/-! # Rule Tactic Descriptions -/

def CasesPattern := AbstractMVarsResult
  deriving Inhabited

inductive CasesTarget
  | decl (decl : Name)
  | patterns (patterns : Array CasesPattern)
  deriving Inhabited

end Aesop
