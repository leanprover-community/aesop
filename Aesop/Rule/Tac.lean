/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleIndex.Basic
import Aesop.Rule.Core
import Aesop.Util

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop

structure RuleTacInput where
  goal : MVarId
  indexMatchLocations : Array IndexMatchLocation
  branchState? : Option RuleBranchState
  deriving Inhabited

/--
Rule tactics must accurately report the following information, which is not
checked:

- `regularGoals`: a collection of unassigned metavariables. These are goals
  produced by the tactic which should be solved by recursive search.
- `unificationGoals`: a collection of unassigned metavariables. These are
  goals produced by the tactic which should be solved by unification.
  `regularGoals` and `unificationGoals` must be disjoint. If a metavariable
  is dependent (i.e. it appears in the target or the local context of
  another goal), then it must appear in `unificationGoals`. Non-dependent
  metavariables are technically allowed to appear in `unificationGoals`, but
  are very unlikely to be solved.
- `postState`: the `MetaM` state after the rule was applied.
-/
structure RuleApplication where
  regularGoals : Array MVarId
  unificationGoals : Array MVarId
  postState : Meta.SavedState
  deriving Inhabited

/--
The result of a rule tactic is a list of rule applications and optionally an
updated branch state. If the branch state is not `none`, it is copied to all
child goals of the rule applications.
-/
structure RuleTacOutput where
  applications : Array RuleApplication
  postBranchState? : Option RuleBranchState

/--
When users want to register a tactic, they may not want to compute all the
information in `RuleTacOutput`. In this case, they can return a
`SimpleRuleTacOutput`, omitting some data, which Aesop then computes for them
(possibly inefficiently since Aesop does not know what the user tactic did).
-/
structure SimpleRuleTacOutput where
  regularGoals : Array MVarId
  unificationGoals : Option (Array MVarId) := none
  deriving Inhabited

@[inline]
def getHypMVars (goal : MVarId) : MetaM (Array MVarId) :=
  withMVarContext goal do
    let mut mvars := #[]
    for hyp in (← getLCtx) do
      mvars := mvars ++ (← getMVarsNoDelayed (mkFVar hyp.fvarId))
    return mvars

@[inline]
def getTargetMVars (goal : MVarId) : MetaM (Array MVarId) := do
  getMVarsNoDelayed (← getMVarType goal)

@[inline]
def getGoalMVars (goal : MVarId) : MetaM (Array MVarId) :=
  return (← getTargetMVars goal) ++ (← getHypMVars goal)

def nondependentAndDependentMVars (ms : Array MVarId) :
    MetaM (Array MVarId × Array MVarId) := do
  let mvarsAppearingInMs ← ms.concatMapM getGoalMVars
  return ms.partition λ m => ¬ mvarsAppearingInMs.contains m

def SimpleRuleTacOutput.toRuleApplication (o : SimpleRuleTacOutput) :
    MetaM RuleApplication := do
  let postState ← saveState
  let (regularGoals, unificationGoals) ←
    match o.unificationGoals with
    | some ugoals => pure (o.regularGoals, ugoals)
    | none => nondependentAndDependentMVars o.regularGoals
  return {
    regularGoals := regularGoals
    unificationGoals := unificationGoals
    postState := postState
  }

/--
A `RuleTac` is the tactic that is run when a rule is applied to a goal.
-/
abbrev RuleTac := RuleTacInput → MetaM RuleTacOutput

abbrev SimpleRuleTac := RuleTacInput → MetaM SimpleRuleTacOutput

def SimpleRuleTac.toRuleTac (t : SimpleRuleTac) : RuleTac := λ input => do
  let output ← t input
  return {
    applications := #[← output.toRuleApplication]
    postBranchState? := input.branchState?
  }

namespace RuleTac

def applyConst (decl : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input => do
  let goals ← apply input.goal (← mkConstWithFreshMVarLevels decl)
  return { regularGoals := goals.toArray }
  -- TODO optimise dependent goal analysis

def applyFVar (userName : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input =>
  withMVarContext input.goal do
    let decl ← getLocalDeclFromUserName userName
    let goals ← apply input.goal (mkFVar decl.fvarId)
    return { regularGoals := goals.toArray }
  -- TODO optimise dependent goal analysis

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

/--
A `GlobalRuleTacBuilderDescr` represents a `GlobalRuleTacBuilder`. When we
serialise the rule set to an olean file, we serialise
`GlobalRuleTacBuilderDescr`s because we can't (currently?) serialise the actual
builders.
-/
inductive GlobalRuleTacBuilderDescr
  | apply (decl : Name)
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

private def checkDeclType (expectedType : Expr) (decl : Name) : MetaM Unit := do
  let actualType ← (← getConstInfo decl).type
  unless (← isDefEq expectedType actualType) do
    throwError "aesop: {decl} was expected to have type{indentExpr expectedType}\nbut has type{indentExpr actualType}"

unsafe def tacticMUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  checkDeclType (← mkAppM ``TacticM #[mkConst ``Unit]) decl
  let tac := SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
      -- It is in principle possible for the environment to change so that
      -- `decl` has a different type at the point where this tactic is called.
      -- We assume that this doesn't happen. Ideally, we would evaluate `tac`
      -- directly after `checkDeclType`, but this fails when
      -- `ofTacticMUnitConstUnsafe` is called by the `@[aesop]` attribute.
    let goals ← runTacticMAsMetaM tac input.goal
    return { regularGoals := goals.toArray }
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.tacticM decl }

@[implementedBy tacticMUnsafe]
constant tacticM : Name → GlobalRuleTacBuilder

unsafe def ruleTacUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  let type ← deltaExpand (mkConst ``RuleTac) λ n => n == ``RuleTac
  checkDeclType type decl
  let tac := λ input => do (← evalConst RuleTac decl) input
    -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.ruleTac decl }

@[implementedBy ruleTacUnsafe]
constant ruleTac : Name → GlobalRuleTacBuilder

unsafe def simpleRuleTacUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  let type ← deltaExpand (mkConst ``SimpleRuleTac) λ n => n == ``SimpleRuleTac
  checkDeclType type decl
  let tac := SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SimpleRuleTac decl
      -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.
    tac input
  return { tac := tac, descr := GlobalRuleTacBuilderDescr.simpleRuleTac decl }

@[implementedBy simpleRuleTacUnsafe]
constant simpleRuleTac : Name → GlobalRuleTacBuilder

def tactic (decl : Name) : GlobalRuleTacBuilder := do
  tacticM decl <|>
  simpleRuleTac decl <|>
  ruleTac decl <|>
  do throwError "aesop: {decl} was expected to be a tactic but it has type{indentExpr (← getConstInfo decl).type}"

def apply (decl : Name) : GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.applyConst decl
    descr := GlobalRuleTacBuilderDescr.apply decl
  }

end GlobalRuleTacBuilder


namespace GlobalRuleTacBuilderDescr

def toRuleTacBuilder : GlobalRuleTacBuilderDescr → GlobalRuleTacBuilder
  | apply decl => GlobalRuleTacBuilder.apply decl
  | tacticM decl => GlobalRuleTacBuilder.tacticM decl
  | simpleRuleTac decl => GlobalRuleTacBuilder.simpleRuleTac decl
  | ruleTac decl => GlobalRuleTacBuilder.ruleTac decl

end GlobalRuleTacBuilderDescr


namespace RuleTacBuilder

def applyFVar (userName : Name) : RuleTacBuilder := λ goal =>
  withMVarContext goal do
    let _ ← getLocalDeclFromUserName userName
      -- Just to check whether the hypothesis exists.
    let tac :=
      { tac := RuleTac.applyFVar userName
        descr := none }
    return (goal, tac)

end RuleTacBuilder

end Aesop
