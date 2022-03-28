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
open Std (HashSet)

namespace Aesop

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

-- Given an array of mvars `gᵢ`, this function separates the `gᵢ` which are
-- proper goals from the `gᵢ` which are proper mvars. A `gᵢ` is a proper mvar
-- iff any goal `gⱼ` depends on it (i.e. `gᵢ` occurs in the target or local
-- context of `gⱼ`). The returned array contains the proper goals and, for each
-- proper goal, the set of proper mvars on which the proper goal depends.
private def analyzeMVars (mvars : Array MVarId) :
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

/-! # Specific Rule Tactics -/

namespace RuleTac

def applyConst (decl : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input => do
  let goals ← apply input.goal (← mkConstWithFreshMVarLevels decl)
  return {
    introducedMVars := IntroducedMVars.raw goals.toArray
    assignedMVars? := none
  }
  -- TODO optimise mvar analysis

def applyFVar (userName : Name) : RuleTac := SimpleRuleTac.toRuleTac λ input =>
  withMVarContext input.goal do
    let decl ← getLocalDeclFromUserName userName
    let goals ← apply input.goal (mkFVar decl.fvarId)
    return {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
  -- TODO optimise mvar analysis

-- Tries to apply each constant in `decls`. For each one that applies, a rule
-- application is returned. If none applies, the tactic fails.
def applyConsts (decls : Array Name) : RuleTac := λ input => do
  let goal := input.goal
  let apps ← decls.filterMapM λ decl => observing? do
    let goals ← apply input.goal (← mkConstWithFreshMVarLevels decl)
    let postState ← saveState
    let rapp := {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
    return (rapp, postState)
  if apps.isEmpty then
    failure
  return { applications := apps, postBranchState? := none }

partial def cases (decl : Name) (isRecursiveType : Bool) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => do
    let goals? ← go #[] #[] input.goal
    match goals? with
    | none => throwError "No hypothesis of type {decl} found"
    | some goals => return {
      introducedMVars := IntroducedMVars.raw goals
      assignedMVars? := none
    }
  where
    findFirstApplicableHyp (excluded : Array FVarId) (goal : MVarId) :
        MetaM (Option FVarId) :=
      withMVarContext goal do
        return (← getLCtx).findDecl? λ ldecl =>
          if ! ldecl.isAuxDecl &&
             ldecl.type.isAppOf decl &&
             ! excluded.contains ldecl.fvarId then
          -- Note: We currently check for occurrences of `decl` structurally,
          -- not up to WHNF.
            some ldecl.fvarId
          else
            none

    go (newGoals : Array MVarId) (excluded : Array FVarId)
        (goal : MVarId) : MetaM (Option (Array MVarId)) := do
      let (some hyp) ← findFirstApplicableHyp excluded goal
        | return none
      try
        let goals ← Meta.cases goal hyp
        let mut newGoals := newGoals
        for g in goals do
          let excluded :=
            if ! isRecursiveType then
              excluded
            else
              let excluded := excluded.map λ fvarId =>
                match g.subst.find? fvarId with
                | some (Expr.fvar fvarId' ..) => fvarId'
                | _ => fvarId
              excluded ++ g.fields.map (·.fvarId!)
          let newGoals? ← go newGoals excluded g.mvarId
          match newGoals? with
          | some newGoals' => newGoals := newGoals'
          | none => newGoals := newGoals.push g.mvarId
        return some newGoals
      catch e =>
        return none

private partial def makeForwardHyps (e : Expr)
    (immediate : UnorderedArraySet Nat) : MetaM (Array Expr) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (argMVars, binderInfos, conclusion) ← forallMetaTelescope type

    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for i in [0:argMVars.size] do
      let mvarId := argMVars[i].mvarId!
      let argName := (← getMVarDecl mvarId).userName
      if immediate.contains i then
        immediateMVars := immediateMVars.push mvarId
      else if binderInfos[i].isInstImplicit then
        instMVars := instMVars.push mvarId

    loop app instMVars immediateMVars 0 #[]
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
      if h : i < immediateMVars.size then
        let mvarId := immediateMVars.get ⟨i, h⟩
        let type := ← getMVarType mvarId

        (← getLCtx).foldlM (init := acc) λ acc ldecl => do
          if ldecl.isAuxDecl then
            return acc
          withoutModifyingState do
            if ← isDefEq ldecl.type type then
              assignExprMVar mvarId (mkFVar ldecl.fvarId)
              loop app instMVars immediateMVars (i + 1) acc
            else
              pure acc
      else
        for instMVar in instMVars do
          let mvarId := instMVar
          let decl ← getMVarDecl mvarId
          let inst ← synthInstance decl.type
          assignExprMVar mvarId inst
        return acc.push (← abstractMVars app).expr

def applyForwardRule (goal : MVarId) (e : Expr) (immediate : UnorderedArraySet Nat) :
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
def forwardExpr (e : Expr) (immediate : UnorderedArraySet Nat) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => withMVarContext input.goal do
    let goal ← applyForwardRule input.goal e immediate
    return {
      introducedMVars := IntroducedMVars.raw #[goal]
      assignedMVars? := none
      -- TODO optimise mvar analysis
    }

def forwardConst (decl : Name) (immediate : UnorderedArraySet Nat) : RuleTac :=
  withApplicationLimit 1 $ forwardExpr (mkConst decl) immediate

def forwardFVar (userName : Name) (immediate : UnorderedArraySet Nat) :
    RuleTac :=
  withApplicationLimit 1 λ input => withMVarContext input.goal do
    let ldecl ← getLocalDeclFromUserName userName
    forwardExpr (mkFVar ldecl.fvarId) immediate input

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
  | forward (decl : Name) (immediate : UnorderedArraySet Nat)
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


def getImmediateNames (e : Expr) : Option (Array Name) →
    MetaM (UnorderedArraySet Nat)
  | none => do
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args and dependent args.
    forallTelescope (← inferType e) λ args _ => do
      let mut result := #[]
      for i in [0:args.size] do
        let fvarId := args[i].fvarId!
        let ldecl ← getLocalDecl fvarId
        let isNondep : MetaM Bool :=
          args.allM (start := i + 1) λ arg =>
            return ! (← getLocalDecl arg.fvarId!).type.containsFVar fvarId
        if ← pure ! ldecl.binderInfo.isInstImplicit <&&> isNondep then
          result := result.push i
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate => do
    forallTelescope (← inferType e) λ args _ => do
      let mut unseen := immediate.deduplicate (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for i in [0:args.size] do
        let argName := (← getLocalDecl args[i].fvarId!).userName
        if immediate.contains argName then
          result := result.push i
          unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "aesop: while registering '{e}' as a forward rule: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result


namespace GlobalRuleTacBuilder

def toRuleTacBuilder (b : GlobalRuleTacBuilder) : RuleTacBuilder := λ goal =>
  return (goal, ← b)

private def checkDeclType (expectedType : Expr) (decl : Name) : MetaM Unit := do
  let actualType := (← getConstInfo decl).type
  unless (← isDefEq expectedType actualType) do
    throwError "aesop: {decl} was expected to have type{indentExpr expectedType}\nbut has type{indentExpr actualType}"

unsafe def tacticMUnsafe (decl : Name) : GlobalRuleTacBuilder := do
  checkDeclType (← mkAppM ``TacticM #[mkConst ``Unit]) decl
  let tac := SimpleRuleTac.toRuleTac λ input => do
    let tac ← evalConst (TacticM Unit) decl
      -- It is in principle possible for the environment to change so that
      -- `decl` has a different type at the point where this tactic is called.
      -- We assume that this doesn't happen. Ideally, we would evaluate `tac`
      -- directly after `checkDeclType`, but this fails when this function is
      -- called by the `@[aesop]` attribute.
    let goals ← runTacticMAsMetaM tac input.goal
    return {
      introducedMVars := IntroducedMVars.raw goals.toArray
      assignedMVars? := none
    }
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

def constructors (constructorNames : Array Name) : GlobalRuleTacBuilder := do
  return {
    tac := RuleTac.applyConsts constructorNames
    descr := GlobalRuleTacBuilderDescr.constructors constructorNames
  }

def cases (decl : Name) (isRecursiveType : Bool) : GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.cases decl isRecursiveType
    descr := GlobalRuleTacBuilderDescr.cases decl isRecursiveType
  }

def forwardCore (decl : Name) (immediate : UnorderedArraySet Nat) :
    GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.forwardConst decl immediate
    descr := GlobalRuleTacBuilderDescr.forward decl immediate
  }

def forward (decl : Name) (immediate : Option (Array Name)) :
    GlobalRuleTacBuilder := do
  forwardCore decl (← getImmediateNames (mkConst decl) immediate)

end GlobalRuleTacBuilder


namespace GlobalRuleTacBuilderDescr

def toRuleTacBuilder : GlobalRuleTacBuilderDescr → GlobalRuleTacBuilder
  | apply decl => GlobalRuleTacBuilder.apply decl
  | constructors cs => GlobalRuleTacBuilder.constructors cs
  | forward decl immediate => GlobalRuleTacBuilder.forwardCore decl immediate
  | cases decl isRecursiveType => GlobalRuleTacBuilder.cases decl isRecursiveType
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

def forwardFVar (userName : Name) (immediate : Option (Array Name)) :
    RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← copyRuleHypotheses goal #[userName] | unreachable!
  withMVarContext goal do
    let immediate ← getImmediateNames (mkFVar newHyp) immediate
    let tac :=
      { tac := RuleTac.forwardFVar (← getLocalDecl newHyp).userName immediate
        descr := none }
    return (goal, tac)

end Aesop.RuleTacBuilder
