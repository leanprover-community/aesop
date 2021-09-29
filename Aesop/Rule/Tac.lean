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

-- Rule tactics must accurately report the following information, which is not
-- checked:
--
-- - `regularGoals`: a collection of unassigned metavariables. These are goals
--    produced by the tactic which should be solved by recursive search.
-- - `unificationGoals`: a collection of unassigned metavariables. These are
--    goals produced by the tactic which should be solved by unification.
--    `regularGoals` and `unificationGoals` must be disjoint. If a metavariable
--    is dependent (i.e. it appears in the target or the local context of
--    another goal), then it must appear in `unificationGoals`. Non-dependent
--    metavariables are technically allowed to appear in `unificationGoals`, but
--    are very unlikely to be solved.
-- - `postState`: the `MetaM` state after the rule was applied.
structure RuleApplication where
  regularGoals : Array MVarId
  unificationGoals : Array MVarId
  postState : Meta.SavedState
  deriving Inhabited

-- The result of a rule tactic is a list of rule applications and optionally an
-- updated branch state. If the branch state is not `none`, it is copied to all
-- child goals of the rule applications.
structure RuleTacOutput where
  applications : Array RuleApplication
  postBranchState? : Option RuleBranchState

-- When users want to register a tactic, they may not want to compute all the
-- information in `RuleTacOutput`. In this case, they can return a
-- `SimpleRuleTacOutput`, omitting some data, which Aesop then computes for them
-- (possibly inefficiently since Aesop does not know what the user tactic did).
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

abbrev RuleTac := RuleTacInput → MetaM RuleTacOutput

abbrev SimpleRuleTac := RuleTacInput → MetaM SimpleRuleTacOutput

def SimpleRuleTac.toRuleTac (t : SimpleRuleTac) : RuleTac := λ input => do
  let output ← t input
  return {
    applications := #[← output.toRuleApplication]
    postBranchState? := input.branchState?
  }

-- A `RuleTacDescr` is a recipe for constructing a `RuleTac`. When we serialise
-- the rule set to an olean file, we serialise `RuleTacDescr`s because we can't
-- (currently?) serialise the actual tactics.
inductive RuleTacDescr
  | applyConst (decl : Name)
  | tacticMUnit (decl : Name)
  | ruleTac (decl : Name)
  | simpleRuleTac (decl : Name)
  deriving Inhabited, BEq

-- A `SerializableRuleTac` bundles a `RuleTacDescr` and the `RuleTac` that was
-- computed from the description. Local rules do not have descriptions since we
-- never serialise them.
structure SerializableRuleTac where
  tac : RuleTac
  descr : Option RuleTacDescr
  deriving Inhabited

namespace RuleTac

private def checkDeclType (expectedType : Expr) (decl : Name) : MetaM Unit := do
  let actualType ← (← getConstInfo decl).type
  unless (← isDefEq expectedType actualType) do
    throwError "aesop: {decl} was expected to have type{indentExpr expectedType}\nbut has type{indentExpr actualType}"

unsafe def ofTacticMUnitConstUnsafe (decl : Name) : MetaM RuleTac := do
  checkDeclType (← mkAppM ``TacticM #[mkConst ``Unit]) decl
  return SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
      -- Note: it is in principle possible for the environment to change so that
      -- `decl` has a different type at the point where this tactic is called.
      -- We assume that this doesn't happen. Ideally, we would evaluate `tac`
      -- directly after `checkDeclType`, but this fails when
      -- `ofTacticMUnitConstUnsafe` is called by the `@[aesop]` attribute.
    let goals ← runTacticMAsMetaM tac input.goal
    return { regularGoals := goals.toArray }

@[implementedBy ofTacticMUnitConstUnsafe]
constant ofTacticMUnitConst : Name → MetaM RuleTac

unsafe def ofRuleTacConstUnsafe (decl : Name) : MetaM RuleTac := do
  let type ← deltaExpand (mkConst ``RuleTac) λ n => n == ``RuleTac
  checkDeclType type decl
  return λ input => do (← evalConst RuleTac decl) input
    -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.

@[implementedBy ofRuleTacConstUnsafe]
constant ofRuleTacConst : Name → MetaM RuleTac

unsafe def ofSimpleRuleTacConstUnsafe (decl : Name) : MetaM RuleTac := do
  let type ← deltaExpand (mkConst ``SimpleRuleTac) λ n => n == ``SimpleRuleTac
  checkDeclType type decl
  return SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst SimpleRuleTac decl
      -- See note about `evalConst` in `ofTacticMUnitConstUnsafe`.
    tac input

@[implementedBy ofSimpleRuleTacConstUnsafe]
constant ofSimpleRuleTacConst : Name → MetaM RuleTac

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


namespace SerializableRuleTac

def ofTacticMUnit (decl : Name) : MetaM SerializableRuleTac :=
  return {
    tac := ← RuleTac.ofTacticMUnitConst decl
    descr := RuleTacDescr.tacticMUnit decl
  }

def ofSimpleRuleTacConst (decl : Name) : MetaM SerializableRuleTac :=
  return {
    tac := ← RuleTac.ofSimpleRuleTacConst decl
    descr := RuleTacDescr.simpleRuleTac decl
  }

def ofRuleTacConst (decl : Name) : MetaM SerializableRuleTac :=
  return {
    tac := ← RuleTac.ofRuleTacConst decl
    descr := RuleTacDescr.ruleTac decl
  }

def ofTacticConst (decl : Name) : MetaM SerializableRuleTac :=
  ofTacticMUnit decl <|>
  ofSimpleRuleTacConst decl <|>
  ofRuleTacConst decl <|>
  do throwError "aesop: {decl} was expected to be a tactic but it has type{indentExpr (← getConstInfo decl).type}"

def applyConst (decl : Name) : MetaM SerializableRuleTac :=
  return {
    tac := RuleTac.applyConst decl
    descr := RuleTacDescr.applyConst decl
  }

def applyFVar (userName : Name) : MetaM SerializableRuleTac := do
  let _ ← getLocalDeclFromUserName userName
    -- This is just to check that the hypothesis exists.
  return {
    tac := RuleTac.applyFVar userName
    descr := none
  }

end SerializableRuleTac

namespace RuleTacDescr

def toRuleTac : RuleTacDescr → MetaM SerializableRuleTac
  | applyConst decl => SerializableRuleTac.applyConst decl
  | tacticMUnit decl => SerializableRuleTac.ofTacticMUnit decl
  | simpleRuleTac decl => SerializableRuleTac.ofSimpleRuleTacConst decl
  | ruleTac decl => SerializableRuleTac.ofRuleTacConst decl

end RuleTacDescr

end Aesop
