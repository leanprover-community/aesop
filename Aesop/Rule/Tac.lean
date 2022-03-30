/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic
import Aesop.Rule.BranchState
import Aesop.Util

open Lean
open Lean.Elab.Tactic
open Lean.Meta
open Std (HashSet)

namespace Aesop

/-! # Rule Tactic Types -/

structure RuleTacInput where
  goal : MVarId
  mvars : Array MVarId
  indexMatchLocations : Array IndexMatchLocation
  branchState? : Option RuleBranchState
  deriving Inhabited

/--
Rules must report all metavariables that were introduced by the rule tactic.
These are exactly the metavariables that

- were not declared before the rule tactic was run;
- are declared and unassigned after the rule tactic was run.

Usually these are just the `MVarId`s returned by a tactic. However, tactics
return two types of metavariables which Aesop distinguishes:

- *Proper mvars* are metavariables that appear in at least one of the reported
  metavariables. These metavariables are solved by unification during the search
  and are not considered Aesop goals.
- *Proper goals* are all reported metavariables that are not proper mvars. These
  are solved by recursive proof search and are considered Aesop goals.

Rules may report the introduced metavariables in two formats:

- The `raw` format reports proper mvars and proper goals as one big list, with
  no distinction between the two. This is the format generally used by Lean
  tactics. When metavariables are reported in this format, Aesop must figure out
  which goals are proper mvars and which are proper goals, which is somewhat
  expensive.

- The `efficient` format distinguishes between proper mvars and proper goals. It
  reports:

  - `goals`: the proper goals, plus for each proper goal the metavariables which
    occur in that goal (including metavariables that were already present before
    the rule was applied).

  - `mvars`: the proper mvars, excluding proper mvars that were already present
    before the rule was applied. (The `RuleInput` specifies these mvars.)
-/
inductive IntroducedMVars
  | raw (mvars : Array MVarId)
  | efficient (goals : Array (MVarId × HashSet MVarId)) (mvars : HashSet MVarId)
  deriving Inhabited

/--
A single rule application, representing the application of a tactic to the input
goal. Must accurately report the following information:

- `introducedMVars`: all metavariables introduced by the tactic. See
  `IntroducedMVars` for details.
- `assignedMVars`: all metavariables that
  - were declared but unassigned before the rule tactic was run;
  - are assigned after the rule tactic was run;
  - are not the goal mvar on which the rule tactic was run.
  If `none`, this set is computed by Aesop.
-/
structure RuleApplication where
  introducedMVars : IntroducedMVars
  assignedMVars? : Option (HashSet MVarId)
  deriving Inhabited

/--
The result of a rule tactic contains:

- `applications`: a list of rule applications and, for each application, a
  snapshot of the `MetaM` state after the tactic was applied.
- `postBranchState?`: an updated branch state. `none` signals that there were
  no changes to the branch state, in which case the input branch state is
  copied to all subgoals.
-/
structure RuleTacOutput where
  applications : Array (RuleApplication × Meta.SavedState)
  postBranchState? : Option RuleBranchState

/--
A `RuleTac` is the tactic that is run when a rule is applied to a goal.
-/
abbrev RuleTac := RuleTacInput → MetaM RuleTacOutput

abbrev SimpleRuleTac := RuleTacInput → MetaM RuleApplication

def SimpleRuleTac.toRuleTac (t : SimpleRuleTac) : RuleTac := λ input => do
  let app ← t input
  let postState ← saveState
  return { applications := #[(app, postState)], postBranchState? := none }


/-! # Metavariable Analysis -/

namespace IntroducedMVars

-- NOTE: Must be called in a MetaM state where the contained metavariables
-- are declared.
def get (previousMVars : Array MVarId) : IntroducedMVars →
    MetaM (Array (MVarId × HashSet MVarId) × HashSet MVarId)
  | raw mvars => do
    let (goals, mvars) ← analyzeMVars mvars
    let mvars := previousMVars.foldl (init := mvars) λ mvars p => mvars.erase p
    return (goals, mvars)
  | efficient goals mvars => return (goals, mvars)
  where
    -- Given an array of mvars `gᵢ`, this function separates the `gᵢ` which are
    -- proper goals from the `gᵢ` which are proper mvars. A `gᵢ` is a proper
    -- mvar iff any goal `gⱼ` depends on it (i.e. `gᵢ` occurs in the target or
    -- local context of `gⱼ`). The returned array contains the proper goals and,
    -- for each proper goal, the set of proper mvars on which the proper goal
    -- depends.
    analyzeMVars (mvars : Array MVarId) :
        MetaM (Array (MVarId × HashSet MVarId) × HashSet MVarId) := do
      let mut goalsAndProperMVars := #[]
      let mut properMVars := HashSet.empty
      for m in mvars do
        let mut mProperMVars ← getGoalMVarsNoDelayed m
        properMVars := properMVars.merge mProperMVars
        goalsAndProperMVars := goalsAndProperMVars.push (m, mProperMVars)
      let properGoals :=
        goalsAndProperMVars.filter λ (g, _) => ! properMVars.contains g
      return (properGoals, properMVars)

def check (preMetaState postMetaState : Meta.SavedState) : IntroducedMVars →
    MetaM Bool
  | raw mvars => return true
  | efficient goals mvars => do
    let actualIntroduced ← introducedExprMVars preMetaState postMetaState
    let r₁ :=
      return actualIntroduced.equalSet (goals.map (·.fst) ++ mvars.toArray)
    let r₂ := goals.allM λ (g, mvars) =>
      return (← getGoalMVarsNoDelayed g) == mvars
    r₁ <&&> r₂

def isEmpty : IntroducedMVars → Bool
  | raw mvars => mvars.isEmpty
  | efficient goals mvars => goals.isEmpty && mvars.isEmpty

end IntroducedMVars


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
        throwError "application limit {n} reached")
    (λ bs => { bs with numApplications := bs.numApplications + 1 })

end RuleTac


/-! # Rule Tactic Builders -/

/--
A `GlobalRuleTacBuilderDescr` represents a `GlobalRuleTacBuilder`. When we
serialise the rule set to an olean file, we serialise
`GlobalRuleTacBuilderDescr`s because we can't (currently?) serialise the actual
builders.
-/
inductive GlobalRuleTacBuilderDescr
  | apply (decl : Name)
  | constructors (constructorNames : Array Name)
  | forward (decl : Name) (immediate : UnorderedArraySet Nat) (clear : Bool)
  | cases (decl : Name) (isRecursiveType : Bool)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | simpleRuleTac (decl : Name)
  deriving Inhabited, BEq

/--
A `RuleTacWithBuilderDescr` bundles a `RuleTac` and optionally the
goal-independent builder which computed the `RuleTac`. Global rules (i.e. those
stored by the `@[aesop]` attribute) always have a builder description, which is
interpreted to deserialise the rule when we deserialise the rule set from an
olean file. Local rules do not have a builder description since they are never
serialised.
-/
structure RuleTacWithBuilderDescr where
  tac : RuleTac
  descr : Option GlobalRuleTacBuilderDescr
  deriving Inhabited

/--
A `GlobalRuleTacBuilder` constructs a global rule, which is independent of
the goal we are trying to solve.
-/
abbrev GlobalRuleTacBuilder := MetaM RuleTacWithBuilderDescr

/--
A `RuleTacBuilder` constructs a global or local rule. Builders for local rules
may depend on and modify the goal we are trying to solve.
-/
abbrev RuleTacBuilder := MVarId → MetaM (MVarId × RuleTacWithBuilderDescr)


namespace GlobalRuleTacBuilder

def toRuleTacBuilder (b : GlobalRuleTacBuilder) : RuleTacBuilder := λ goal =>
  return (goal, ← b)

end GlobalRuleTacBuilder


namespace RuleTacBuilder

def copyRuleHypotheses (goal : MVarId) (userNames : Array Name) :
    MetaM (MVarId × Array FVarId) := do
  let newHyps ← userNames.mapM λ n => do
    let decl ← getLocalDeclFromUserName n
    pure {
      userName := `_local ++ n -- TODO potential for name clashes
      value := mkFVar decl.fvarId
      type := decl.type
      binderInfo := BinderInfo.auxDecl
    }
  let (newHyps, goal) ← assertHypothesesWithBinderInfos goal newHyps
  return (goal, newHyps)

end Aesop.RuleTacBuilder
