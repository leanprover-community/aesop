/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Rule.BranchState
import Aesop.Util

open Lean
open Lean.Elab.Tactic
open Lean.Meta
open Std (HashSet)

namespace Aesop

/-! # Helper Functions for Analyzing Rule Tactic MVars  -/

/--
Given a list of mvars `gᵢ`, this function separates the `gᵢ` which are
proper goals from the `gᵢ` which are proper mvars. A `gᵢ` is a proper mvar iff
any goal `gⱼ` depends on it (i.e. `gᵢ` occurs in the target or local context of
`gⱼ`). The returned array contains the proper goals and, for each proper goal,
the set of proper mvars on which the proper goal depends.
-/
private def getProperGoalsAndMVars [ForIn MetaM ρ MVarId] (mvars : ρ) :
    MetaM (Array (MVarId × HashSet MVarId) × HashSet MVarId) := do
  let mut goalsAndProperMVars := #[]
  let mut properMVars := HashSet.empty
  for m in mvars do
    let mProperMVars ← getGoalMVarsNoDelayed m
    properMVars := properMVars.merge mProperMVars
    goalsAndProperMVars := goalsAndProperMVars.push (m, mProperMVars)
  let properGoals :=
    goalsAndProperMVars.filter λ (g, _) => ! properMVars.contains g
  return (properGoals, properMVars)

@[specialize]
def getProperGoalsAndNewMVars [ForIn MetaM ρ MVarId]
    (previousMVars : Array MVarId) (mvars : ρ) :
    MetaM (Array (MVarId × HashSet MVarId) × HashSet MVarId) := do
  let (goals, mvars) ← getProperGoalsAndMVars mvars
  let mvars := previousMVars.foldl (init := mvars) λ mvars m => mvars.erase m
  return (goals, mvars)

def getAssignedMVars (previousMVars : Array MVarId) :
    MetaM (HashSet MVarId) := do
  let mut result := {}
  for m in previousMVars do
    if ← isExprMVarAssigned m <||> isDelayedAssigned m then
      result := result.insert m
  return result


/-! # Rule Tactic Types -/

structure RuleTacInput where
  goal : MVarId
  mvars : Array MVarId
  indexMatchLocations : UnorderedArraySet IndexMatchLocation
  branchState? : Option RuleBranchState
  deriving Inhabited

/--
A single rule application, representing the application of a tactic to the input
goal. Must accurately report the following information:

- `postState`: the `MetaM` state after the tactic was run.
- `goals`: the proper goals introduced by the tactic (see below) plus, for each
  goal, the set of proper metavariables which appear in the goal (either in a
  hypothesis or in the target).
- `introducedMVars`: the proper metavariables introduced by the tactic (see
  below).
- `assignedMVars`: all metavariables that
  - were declared but unassigned before the tactic was run;
  - are assigned after the tactic was run;
  - are not the goal mvar on which the tactic was run.

Metavariables introduced by the tactic are classified as either *proper goals*
or *proper metavariables*. Let `ms` be the set of metavariables introduced by
the tactic. Then the proper metavariables are those `m ∈ ms` for which there is
an `m' ∈ ms` such that `m` appears in the goal of `m'` (either in a hypothesis
or in the target). The proper goals are the elements of `ms` which are not
proper metavariables.

Exception: proper goals need not necessarily have been introduced by the tactic.
A tactic may return the same goal it was called on, doing nothing. Proper
metavariables, on the other hand, must have been introduced by the tactic.
-/
structure RuleApplication where
  goals : Array (MVarId × HashSet MVarId)
  postState : Meta.SavedState
  introducedMVars : HashSet MVarId
  assignedMVars : HashSet MVarId
  deriving Inhabited

namespace RuleApplication

def check (input : RuleTacInput) (r : RuleApplication)
    (preState : Meta.SavedState) : MetaM (Option MessageData) :=
  r.postState.runMetaM' do
    let reportedIntroduced := r.introducedMVars.toArray
    let actualIntroduced ← introducedExprMVars preState r.postState
    let actualIntroduced :=
      r.goals.foldl (init := actualIntroduced) λ actualIntroduced (m, _) =>
        actualIntroduced.erase m
    if ! actualIntroduced.equalSet reportedIntroduced then
      return some m!"rule reported wrong introduced metavariables.\nReported: {reportedIntroduced.map (·.name)}\nActual: {actualIntroduced.map (·.name)}"
    let reportedAssigned := r.assignedMVars.toArray
    let actualAssigned :=
      (← assignedExprMVars preState r.postState).erase input.goal
    if ! actualAssigned.equalSet reportedAssigned then
      return some m!"rule reported wrong assigned metavariables.\nReported: {reportedAssigned.map (·.name)}\nActual: {actualAssigned.map (·.name)}"
    for (goal, mvars) in r.goals do
      if ← isExprMVarAssigned goal <||> isDelayedAssigned goal then
        return some m!"subgoal metavariable {goal.name} is already assigned."
      let actualMVars ← getGoalMVarsNoDelayed goal
      if ! actualMVars == mvars then
        return some m!"rule reported wrong metavariables for goal {goal.name}.\nReported: {mvars.toArray.map (·.name)}\nActual: {actualMVars.toArray.map (·.name)}"
    return none

end RuleApplication

/--
The result of a rule tactic contains:

- `applications`: a list of rule applications.
- `postBranchState?`: an updated branch state. `none` signals that there were
  no changes to the branch state, in which case the input branch state is
  copied to all subgoals.
-/
structure RuleTacOutput where
  applications : Array RuleApplication
  postBranchState? : Option RuleBranchState
  deriving Inhabited


/--
A `RuleTac` is the tactic that is run when a rule is applied to a goal.
-/
abbrev RuleTac := RuleTacInput → MetaM RuleTacOutput

abbrev SimpleRuleTac := RuleTacInput → MetaM (List MVarId)

def SimpleRuleTac.toRuleTac (t : SimpleRuleTac) : RuleTac := λ input => do
  let goals ← t input
  let postState ← saveState
  let (goals, introducedMVars) ← getProperGoalsAndNewMVars input.mvars goals
  let assignedMVars ← getAssignedMVars input.mvars
  let app := { postState, goals, introducedMVars, assignedMVars }
  return { applications := #[app], postBranchState? := none }


/-! # Branch State -/

namespace RuleTac

@[inline]
def withBranchState (check : RuleBranchState → MetaM Unit)
    (modify : RuleBranchState → RuleBranchState) (r : RuleTac) :
    RuleTac := λ input => do
  let initialBranchState := input.branchState?.getD RuleBranchState.initial
  check initialBranchState
  let output ← r input
  let newBranchState := modify $ output.postBranchState?.getD initialBranchState
  return { output with postBranchState? := some newBranchState }

def withApplicationLimit (n : Nat) : RuleTac → RuleTac :=
  withBranchState
    (λ bs => do
      if bs.numApplications >= n then
        throwError "Rule is limited to {n} application(s) per branch.")
    (λ bs => { bs with numApplications := bs.numApplications + 1 })

end RuleTac


/-! # Rule Tactic Descriptions -/

inductive RuleTacDescr
  | applyConst (decl     : Name)
  | applyFVar  (userName : Name)
  | constructors (constructorNames : Array Name)
  | forwardConst (decl     : Name) (immediate : UnorderedArraySet Nat) (clear : Bool)
  | forwardFVar  (userName : Name) (immediate : UnorderedArraySet Nat) (clear : Bool)
  | cases (decl : Name) (isRecursiveType : Bool)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | simpleRuleTac (decl : Name)
  deriving Inhabited

namespace RuleTacDescr

def isGlobal : RuleTacDescr → Bool
  | applyConst .. => true
  | applyFVar .. => false
  | constructors .. => true
  | forwardConst .. => true
  | forwardFVar .. => false
  | cases .. => true
  | tacticM .. => true
  | ruleTac .. => true
  | simpleRuleTac .. => true

end RuleTacDescr


/-! # Miscellany -/

def copyRuleHypotheses (goal : MVarId) (userNames : Array Name) :
    MetaM (MVarId × Array FVarId) := do
  let newHyps ← userNames.mapM λ n => do
    let decl ← getLocalDeclFromUserName n
    pure {
      userName := ← mkFreshUserName $ `_local ++ n
      value := mkFVar decl.fvarId
      type := decl.type
      binderInfo := BinderInfo.auxDecl
    }
  let (newHyps, goal) ← assertHypothesesWithBinderInfos goal newHyps
  return (goal, newHyps)

def copyRuleHypothesis (goal : MVarId) (userName : Name) :
    MetaM (MVarId × FVarId) := do
  let (goal, #[hyp]) ← copyRuleHypotheses goal #[userName]
    | unreachable!
  return (goal, hyp)

end Aesop
