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

private partial def makeForwardHyps (e : Expr) (immediate : Array Name) : MetaM (Array Expr) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (argMVars, binderInfos, conclusion) ← forallMetaTelescope type

    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for i in [0:argMVars.size] do
      let mvar := argMVars[i]
      let mvarId := mvar.mvarId!
      let argName := (← getMVarDecl mvarId).userName
      if immediate.contains argName then
        immediateMVars := immediateMVars.push mvarId
      else if binderInfos[i].isInstImplicit then
        instMVars := instMVars.push mvarId

    loop app instMVars immediateMVars 0 #[]
  where
    finalizeApplication (app : Expr) (instMVars : Array MVarId) : MetaM Expr := do
      for instMVar in instMVars do
        let mvarId := instMVar
        let decl ← getMVarDecl mvarId
        let inst ← synthInstance decl.type
        assignExprMVar mvarId inst

      return (← abstractMVars app).expr

    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId) (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
      if i < immediateMVars.size then
        let mvarId := immediateMVars[i]
        let argDecl ← getMVarDecl mvarId
        let lctx ← getLCtx

        lctx.foldlM (init := acc) λ acc ldecl => do
          if ldecl.isAuxDecl then return acc
          withoutModifyingState do
            if ← isDefEq ldecl.type argDecl.type then
              assignExprMVar mvarId (mkFVar ldecl.fvarId)
              loop app instMVars immediateMVars (i + 1) acc
            else
              pure acc
      else
        let app ← finalizeApplication app instMVars
        return acc.push app

def applyForwardRule (goal : MVarId) (e : Expr) (immediate : Array Name) :
    MetaM MVarId :=
  withMVarContext goal do
    let newHyps ← makeForwardHyps e immediate
    let userNames ← getUnusedUserNames newHyps.size `fwd
    let (_, goal) ← assertHypotheses goal $ ← newHyps.mapIdxM λ i val =>
      return {
        userName := userNames[i]
        value := val
        type := ← inferType val
      }
    return goal

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

@[inline]
def forwardExpr (e : Expr) (immediate : Array Name) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => withMVarContext input.goal do
    let goal ← applyForwardRule input.goal e immediate
    return { regularGoals := #[goal] }

def forwardConst (decl : Name) (immediate : Array Name) : RuleTac :=
  withApplicationLimit 1 $ forwardExpr (mkConst decl) immediate

def forwardFVar (userName : Name) (immediate : Array Name) : RuleTac :=
  withApplicationLimit 1 λ input => withMVarContext input.goal do
    let ldecl ← getLocalDeclFromUserName userName
    forwardExpr (mkFVar ldecl.fvarId) immediate input

end RuleTac

/--
A `GlobalRuleTacBuilderDescr` represents a `GlobalRuleTacBuilder`. When we
serialise the rule set to an olean file, we serialise
`GlobalRuleTacBuilderDescr`s because we can't (currently?) serialise the actual
builders.
-/
inductive GlobalRuleTacBuilderDescr
  | apply (decl : Name)
  | forward (decl : Name) (immediate : Array Name)
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


private def checkImmediateNames (e : Expr) (immediate : Array Name) :
    MetaM Unit := do
  let type ← inferType e
  forallTelescope type λ args _ => do
    let argNames ← args.mapM λ fvar =>
      return (← getFVarLocalDecl fvar).userName
    for iName in immediate do
      unless argNames.contains iName do
        throwError "aesop: while registering '{e}' as a forward rule: function does not have an argument named '{iName}'"


namespace GlobalRuleTacBuilder

def forward (decl : Name) (immediate : Array Name) :
    GlobalRuleTacBuilder := do
  checkImmediateNames (mkConst decl) immediate
  return {
    tac := RuleTac.forwardConst decl immediate
    descr := GlobalRuleTacBuilderDescr.forward decl immediate
  }

end GlobalRuleTacBuilder


namespace GlobalRuleTacBuilderDescr

def toRuleTacBuilder : GlobalRuleTacBuilderDescr → GlobalRuleTacBuilder
  | apply decl => GlobalRuleTacBuilder.apply decl
  | forward decl immediate => GlobalRuleTacBuilder.forward decl immediate
  | tacticM decl => GlobalRuleTacBuilder.tacticM decl
  | simpleRuleTac decl => GlobalRuleTacBuilder.simpleRuleTac decl
  | ruleTac decl => GlobalRuleTacBuilder.ruleTac decl

end GlobalRuleTacBuilderDescr


namespace RuleTacBuilder

private def copyRuleHypotheses (goal : MVarId) (userNames : Array Name) :
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

def applyFVar (userName : Name) : RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← copyRuleHypotheses goal #[userName] | unreachable!
  withMVarContext goal do
    let tac :=
      { tac := RuleTac.applyFVar (← getLocalDecl newHyp).userName
        descr := none }
    return (goal, tac)

def forwardFVar (userName : Name) (immediate : Array Name) :
    RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← copyRuleHypotheses goal #[userName] | unreachable!
  withMVarContext goal do
    checkImmediateNames (mkFVar newHyp) immediate
    let tac :=
      { tac := RuleTac.forwardFVar (← getLocalDecl newHyp).userName immediate
        descr := none }
    return (goal, tac)

end RuleTacBuilder

end Aesop
