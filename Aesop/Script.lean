/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic
import Aesop.Util.Tactic
import Aesop.Util.EqualUpToIds
import Std.Lean.Meta.Clear
import Std.Lean.Meta.Inaccessible
import Std.Lean.HashSet

open Lean
open Lean.Elab.Tactic
open Lean.Meta
open Lean.Parser.Tactic
open Lean.PrettyPrinter

namespace Aesop

-- FIXME remove
elab (name := Parser.onGoal) "on_goal " n:num " => " ts:tacticSeq : tactic => do
  let gs := (← getGoals).toArray
  let n := n.getNat
  if n == 0 then
    throwError "on_goal: goal numbers start at 1, so 0 is not a valid goal number"
  if h : n - 1 < gs.size then
    let g := gs[n - 1]
    setGoals [g]
    evalTactic ts
    let gs := gs[:n - 1] ++ (← getUnsolvedGoals).toArray ++ gs[n:]
    setGoals gs.toList
  else
    throwError "on_goal: tried to select goal {n} but there are only {gs.size} goals"

@[inline]
private def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1

structure GoalWithMVars where
  goal : MVarId
  mvars : HashSet MVarId
  deriving Inhabited

instance : Repr GoalWithMVars where
  reprPrec
    | g, _ => s!"\{ goal := {repr g.goal}, mvars := {repr g.mvars.toArray} }"

instance : BEq GoalWithMVars :=
  ⟨λ g₁ g₂ => g₁.goal == g₂.goal⟩


def GoalWithMVars.ofMVarId (goal : MVarId) : MetaM GoalWithMVars := do
  return { goal, mvars := ← goal.getMVarDependencies }



variable [Monad m] [MonadQuotation m] [MonadError m]


def UnstructuredScriptBuilder (m : Type _ → Type _) := m (Array Syntax.Tactic)

namespace UnstructuredScriptBuilder


@[inline]
def run (b : UnstructuredScriptBuilder m) : m (Array Syntax.Tactic) :=
  b

@[inline]
def ofTactics (ts : m (Array Syntax.Tactic)) : UnstructuredScriptBuilder m :=
  return (← ts)

@[inline]
def ofTactic (t : m Syntax.Tactic) : UnstructuredScriptBuilder m :=
  return #[← t]

@[inline]
def seq (b₁ b₂ : UnstructuredScriptBuilder m) : UnstructuredScriptBuilder m :=
  return (← b₁.run) ++ (← b₂.run)

@[inline]
def focusAndDoneEach (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  bs.mapM λ b => do `(tactic| { $(← b.run):tactic* })

@[inline]
def seqFocusAndDone (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) : UnstructuredScriptBuilder m :=
  b.seq (.focusAndDoneEach bs)

@[inline]
def seqFocus (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  let ts ← b.run
  if bs.size == 0 then
    return ts
  let tss ← bs.mapM (·.run)
  if tss.all (·.isEmpty) then
    return ts
  if h : tss.size = 1 then
    let ts₂ := tss[0]'(by simp [h])
    return ts.push (← `(tactic| focus $ts₂:tactic*))
  else
    let tss ← tss.mapM λ (ts₂ : Array Syntax.Tactic) =>
      if ts₂.isEmpty then
        `(tactic| skip)
      else
        `(tactic| ($ts₂:tactic*))
    if let (some t) := ts[ts.size - 1]? then
      return ts.pop.push (← `(tactic| $t:tactic <;> [ $tss;* ]))
    else
      return #[← `(tactic| map_tacs [ $tss;* ])]

@[inline]
protected def id : UnstructuredScriptBuilder m :=
  return #[]

instance [Pure m] : Inhabited (UnstructuredScriptBuilder m) :=
  ⟨pure #[]⟩

end UnstructuredScriptBuilder


structure StructuredScriptBuilder (m : Type → Type) where
  subgoals : Nat
  elim : Subarray (UnstructuredScriptBuilder m) → UnstructuredScriptBuilder m

namespace StructuredScriptBuilder

@[inline]
def run (b : StructuredScriptBuilder m) : m (Array Syntax.Tactic) :=
  b.elim #[].toSubarray

private def ensureContsSize (conts : Subarray α) (subgoals : Nat) :
    m (PLift (conts.size = subgoals)) := do
  if h : conts.size = subgoals then
    return ⟨h⟩
  else
    throwError "while building tactic syntax: tactic has {subgoals} subgoals but was given {conts.size} continuation tactics"

protected def id : StructuredScriptBuilder m where
  subgoals := 1
  elim conts := do
    let ⟨hconts⟩ ← ensureContsSize conts 1
    conts[0]'(by simp [hconts])

def ofTactics (subgoals : Nat) (ts : m (Array Syntax.Tactic)) :
    StructuredScriptBuilder m where
  subgoals := subgoals
  elim conts := do
    let ⟨hconts⟩ ← ensureContsSize conts subgoals
    if subgoals = 0 then
      UnstructuredScriptBuilder.ofTactics ts
    else if h : subgoals = 1 then
      UnstructuredScriptBuilder.ofTactics ts |>.seq (conts[0]'(by simp [*]))
    else
      UnstructuredScriptBuilder.ofTactics ts |>.seqFocusAndDone conts

@[inline]
def ofUnstructuredScriptBuilder (subgoals : Nat)
    (b : UnstructuredScriptBuilder m) : StructuredScriptBuilder m :=
  .ofTactics subgoals b

@[inline]
def ofTactic (subgoals : Nat) (t : m Syntax.Tactic) :
    StructuredScriptBuilder m :=
  .ofTactics subgoals (return #[← t])

@[inline]
def done : StructuredScriptBuilder m :=
  .ofTactics 0 (return #[])

instance : Inhabited (StructuredScriptBuilder m) :=
  ⟨.id⟩

def error (msg : MessageData) : StructuredScriptBuilder m where
  subgoals := 0
  elim _ := throwError "Unable to build tactic syntax: {msg}"

def seq (b : StructuredScriptBuilder m)
    (bs : Array (StructuredScriptBuilder m)) : StructuredScriptBuilder m :=
  let subgoals := bs.foldl (init := 0) λ n b => n + b.subgoals
  { subgoals
    elim := λ conts => do
      discard $ ensureContsSize bs.toSubarray b.subgoals
      discard $ ensureContsSize conts subgoals
      let mut bConts := Array.mkEmpty b.subgoals
      let mut start := 0
      for b' in bs do
        let «end» := start + b'.subgoals
        let b'Conts := conts[start:«end»]
        start := «end»
        bConts := bConts.push (b.elim b'Conts)
      b.elim bConts.toSubarray
  }

end StructuredScriptBuilder


structure ScriptBuilder (m) where
  unstructured : UnstructuredScriptBuilder m
  structured : StructuredScriptBuilder m

instance [Pure m] : Inhabited (ScriptBuilder m) :=
  ⟨default, default⟩

namespace ScriptBuilder

protected def id : ScriptBuilder m where
  unstructured := .id
  structured := .id

def ofTactics (subgoals : Nat) (ts : m (Array Syntax.Tactic)) :
    ScriptBuilder m where
  unstructured := .ofTactics ts
  structured := .ofTactics subgoals ts

@[inline]
def ofUnstructuredScriptBuilder (subgoals : Nat)
    (b : UnstructuredScriptBuilder m) : ScriptBuilder m :=
  .ofTactics subgoals b

def ofTactic (subgoals : Nat) (t : m Syntax.Tactic) : ScriptBuilder m where
  unstructured := .ofTactic t
  structured := .ofTactic subgoals t

def seq (b : ScriptBuilder m) (bs : Array (ScriptBuilder m)) :
    ScriptBuilder m where
  unstructured := b.unstructured.seqFocus $ bs.map (·.unstructured)
  structured := b.structured.seq $ bs.map (·.structured)

def assertHypotheses (goal : MVarId) (hs : Array Hypothesis) :
    ScriptBuilder MetaM :=
  .ofTactics 1 $ goal.withContext $ hs.mapM λ h => do
    `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))

def clear (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptBuilder MetaM :=
  .ofTactic 1 $ goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    `(tactic| clear $userNames*)

def unhygienicAesopCases (goal : MVarId) (fvarId : FVarId) (subgoals : Nat) :
    ScriptBuilder MetaM :=
  .ofTactic subgoals do
    let userName ← goal.withContext fvarId.getUserName
    `(tactic| unhygienic aesop_cases $(mkIdent userName):ident)

def renameInaccessibleFVars (goal : MVarId) (renamedFVars : Array FVarId) :
    ScriptBuilder MetaM :=
  if renamedFVars.isEmpty then
    .id
  else
    .ofTactic 1 $ goal.withContext do
      let ids ← renamedFVars.mapM λ fvarId => do
        let userName := mkIdent (← fvarId.getDecl).userName
        `(binderIdent| $userName:ident)
      `(tactic| rename_i $ids:binderIdent*)

def unfoldManyStar (usedDecls : HashSet Name) : ScriptBuilder MetaM :=
  if usedDecls.isEmpty then
    .id
  else
    .ofTactic 1 `(tactic| aesop_unfold [$(usedDecls.toArray.map mkIdent):ident,*])

def unhygienicExt (subgoals : Nat) : ScriptBuilder MetaM :=
  .ofTactic subgoals `(tactic| unhygienic ext)

@[inline, always_inline]
def withPrefix (f : TSyntax ``tacticSeq → m (Array (TSyntax `tactic)))
    (b : ScriptBuilder m) : ScriptBuilder m where
  unstructured := do
    let ts ← b.unstructured
    f (← `(tacticSeq| $ts:tactic*))
  structured := {
    subgoals := b.structured.subgoals
    elim := λ ks => do
      let ts ← b.structured.elim ks
      f (← `(tacticSeq| $ts:tactic*))
  }

protected def withTransparency (md : TransparencyMode) (b : ScriptBuilder m) :
    ScriptBuilder m :=
  b.withPrefix λ ts =>
    return #[← `(tactic| ($(← withTransparencySeqSyntax md ts)))]

protected def withAllTransparency (md : TransparencyMode) (b : ScriptBuilder m) :
    ScriptBuilder m :=
  b.withPrefix λ ts =>
    return #[← `(tactic| ($(← withAllTransparencySeqSyntax md ts)))]

end ScriptBuilder

abbrev RuleTacScriptBuilder := ScriptBuilder MetaM

@[inline, always_inline]
def mkScriptBuilder? (generateScript : Bool)
    (builder : ScriptBuilder MetaM) : Option (ScriptBuilder MetaM) :=
  if generateScript then
    some builder
  else
    none

def assertHypothesesWithScript (goal : MVarId)
    (hs : Array Hypothesis) (generateScript : Bool) :
    MetaM (Array FVarId × MVarId × Option (ScriptBuilder MetaM)) := do
  let (fvarIds, goal') ← goal.assertHypotheses hs
  let scriptBuilder? := mkScriptBuilder? generateScript $ .assertHypotheses goal hs
  return (fvarIds, goal', scriptBuilder?)

def clearWithScript (goal : MVarId) (fvarId : FVarId) (generateScript : Bool) :
    MetaM (MVarId × Option (ScriptBuilder MetaM)) :=
  let scriptBuilder? := mkScriptBuilder? generateScript $ .clear goal #[fvarId]
  return (← goal.clear fvarId, scriptBuilder?)

def tryClearWithScript (goal : MVarId) (fvarId : FVarId) (generateScript : Bool) :
    MetaM (MVarId × Option (ScriptBuilder MetaM)) := do
  let goal' ← goal.tryClear fvarId
  let scriptBuilder? := mkScriptBuilder? generateScript $
    if goal' == goal then
      .id
    else
      .clear goal #[fvarId]
  return (goal', scriptBuilder?)

def tryClearManyWithScript (goal : MVarId) (fvarIds : Array FVarId)
    (generateScript : Bool) :
    MetaM (MVarId × Array FVarId × Option (ScriptBuilder MetaM)) := do
  let (goal', cleared) ← goal.tryClearMany' fvarIds
  let scriptBuilder? := mkScriptBuilder? generateScript $ .clear goal cleared
  return (goal', cleared, scriptBuilder?)

def unhygienicCasesWithScript (goal : MVarId) (fvarId : FVarId)
    (generateScript : Bool) :
    MetaM (Array CasesSubgoal × Option (ScriptBuilder MetaM)) := do
  let goals ← unhygienic $ goal.cases fvarId
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .unhygienicAesopCases goal fvarId goals.size
  return (goals, scriptBuilder?)

def renameInaccessibleFVarsWithScript (goal : MVarId) (generateScript : Bool) :
    MetaM (MVarId × Array FVarId × Option (ScriptBuilder MetaM)) := do
  let (goal, renamedFVars) ← goal.renameInaccessibleFVars
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .renameInaccessibleFVars goal renamedFVars
  return (goal, renamedFVars, scriptBuilder?)

def unfoldManyStarWithScript (goal : MVarId)
    (unfold? : Name → Option (Option Name)) (generateScript : Bool) :
    MetaM (UnfoldResult MVarId × Option (ScriptBuilder MetaM)) := do
  let result ← unfoldManyStar goal unfold?
  let scriptBuilder? := mkScriptBuilder? generateScript $
    .unfoldManyStar result.usedDecls
  return (result, scriptBuilder?)


private def throwUnknownGoalError (goal : MVarId) (pre : MessageData) : m α :=
  throwError "internal error: {pre}: unknown goal '?{goal.name}'"


structure TacticState where
  visibleGoals : Array GoalWithMVars
  invisibleGoals : HashSet MVarId
  deriving Inhabited

namespace TacticState

variable [Monad m] [MonadError m]

def getVisibleGoalIndex? (ts : TacticState) (goal : MVarId) : Option Nat :=
  ts.visibleGoals.findIdx? (·.goal == goal)

def getVisibleGoalIndex (ts : TacticState) (goal : MVarId) : m Nat := do
  if let (some idx) := ts.getVisibleGoalIndex? goal then
    return idx
  else
    throwUnknownGoalError goal "getVisibleGoalIndex"

def getMainGoal? (ts : TacticState) : Option MVarId :=
  ts.visibleGoals[0]?.map (·.goal)

def hasNoVisibleGoals (ts : TacticState) : Bool :=
  ts.visibleGoals.isEmpty

def hasSingleVisibleGoal (ts : TacticState) : Bool :=
  ts.visibleGoals.size == 1

def visibleGoalsHaveMVars (ts : TacticState) : Bool :=
  ts.visibleGoals.any λ g => ! g.mvars.isEmpty

private def replaceWithArray [BEq α] (xs : Array α) (x : α) (r : Array α) :
    Option (Array α) := Id.run do
  let mut found := false
  let mut ys := Array.mkEmpty (xs.size - 1 + r.size)
  for x' in xs do
    if x' == x then
      ys := ys ++ r
      found := true
    else
      ys := ys.push x'
  return if found then some ys else none

def eraseSolvedGoals (ts : TacticState) (mctx : MetavarContext) :
    TacticState := {
  ts with
  visibleGoals :=
    ts.visibleGoals.filter (! mctx.isExprMVarAssignedOrDelayedAssigned ·.goal)
  invisibleGoals :=
    HashSet.filter ts.invisibleGoals
      (! mctx.isExprMVarAssignedOrDelayedAssigned ·)
}

def applyTactic (ts : TacticState) (inGoal : MVarId)
    (outGoals : Array GoalWithMVars) (postMCtx : MetavarContext) :
    m TacticState := do
  let (some visibleGoals) :=
        replaceWithArray ts.visibleGoals ⟨inGoal, {}⟩ outGoals
    | throwUnknownGoalError inGoal "applyTactic"
  let ts := { ts with visibleGoals }
  return eraseSolvedGoals ts postMCtx

-- Focus the visible goal `goal` and move all other previously visible goals
-- to `invisibleGoals`.
def focus (ts : TacticState) (goal : MVarId) : m TacticState := do
  let (some goalWithMVars) := ts.visibleGoals.find? (·.goal == goal)
    | throwUnknownGoalError goal "focus"
  let mut invisibleGoals := ts.invisibleGoals
  for g in ts.visibleGoals do
    if g.goal != goal then
      invisibleGoals := invisibleGoals.insert g.goal
  return { visibleGoals := #[goalWithMVars], invisibleGoals }

@[inline, always_inline]
def onGoalM (ts : TacticState) (g : MVarId)
    (f : TacticState → m (α × TacticState)) : m (α × TacticState) := do
  let (a, postTs) ← f (← ts.focus g)
  let mut visibleGoals := #[]
  for preGoal in ts.visibleGoals do
    if preGoal.goal == g then
      visibleGoals := visibleGoals ++ postTs.visibleGoals
    else if postTs.invisibleGoals.contains preGoal.goal then
      visibleGoals := visibleGoals.push preGoal
  return (a, { visibleGoals, invisibleGoals := postTs.invisibleGoals })

end TacticState


structure TacticInvocation where
  preState : Meta.SavedState
  preGoal : MVarId
  tacticSeq : Array Syntax.Tactic
  postGoals : Array GoalWithMVars
  postState : Meta.SavedState
  deriving Nonempty

def TacticState.applyTacticInvocation (tacticState : TacticState)
    (ti : TacticInvocation) : m TacticState :=
  tacticState.applyTactic ti.preGoal ti.postGoals ti.postState.meta.mctx

namespace TacticInvocation

def noop (preGoal : MVarId) (postGoal : GoalWithMVars)
    (preState postState : Meta.SavedState) : TacticInvocation := {
  tacticSeq := #[]
  postGoals := #[postGoal]
  preGoal, preState, postState
}

def render (acc : Array Syntax.Tactic) (ti : TacticInvocation)
    (tacticState : TacticState) : m (Array Syntax.Tactic × TacticState) := do
  if ti.tacticSeq.size == 0 then
    let tacticState ← tacticState.applyTacticInvocation ti
    return (acc, tacticState)
  else
    let pos ← tacticState.getVisibleGoalIndex ti.preGoal
    let tacticState ← tacticState.applyTacticInvocation ti
    if pos == 0 then
      return (acc ++ ti.tacticSeq, tacticState)
    else
      let posLit := mkOneBasedNumLit pos
      let t ← `(tactic| on_goal $posLit:num => $(ti.tacticSeq):tactic*)
      return (acc.push t, tacticState)

def validate (ti : TacticInvocation) : MetaM Unit := do
  let preMCtx := ti.preState.meta.mctx
  let expectedPostMCtx := ti.postState.meta.mctx
  let expectedPostGoals := ti.postGoals |>.map (·.goal)
  let tac ← `(Lean.Parser.Tactic.tacticSeq| $ti.tacticSeq*)
  let (actualPostState, actualPostGoals) ←
    try
      runTacticMCapturingPostState (evalTactic tac) ti.preState [ti.preGoal]
    catch e =>
      throwError "tactic{indentD tac}\nfailed with error{indentD e.toMessageData}"
  let actualPostGoals := actualPostGoals.toArray
  unless ← tacticStatesEqualUpToIds preMCtx expectedPostMCtx
      actualPostState.meta.mctx expectedPostGoals actualPostGoals do
    throwError "tactic{indentD tac}\nsucceeded but did not generate expected state. Initial goal:{indentD $ ← fmtGoals ti.preState #[ti.preGoal]}\nExpected goals:{indentD $ ← fmtGoals ti.postState $ ti.postGoals.map (·.goal)}\nActual goals:{indentD $ ← fmtGoals actualPostState actualPostGoals}"
where
  fmtGoals (state : Meta.SavedState) (goals : Array MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $
        MessageData.joinSep (← goals.mapM (λ g => return m!"{g}")).toList "\n"

end TacticInvocation


abbrev UnstructuredScript := Array TacticInvocation

def UnstructuredScript.render (tacticState : TacticState)
    (s : UnstructuredScript) : m (Array Syntax.Tactic) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState := tacticState
  for ti in s do
    let (script', tacticState') ← ti.render script tacticState
    script := script'
    tacticState := tacticState'
  return script

def UnstructuredScript.validate (s : UnstructuredScript) : MetaM Unit :=
  s.forM (·.validate)

inductive StructuredScript
  | empty
  | unstructuredStep (ti : TacticInvocation) (tail : StructuredScript)
  | solve (goal : MVarId) (here tail : StructuredScript)
  deriving Inhabited

def StructuredScript.render (tacticState : TacticState)
    (script : StructuredScript) : m (Array Syntax.Tactic) := do
  (·.fst) <$> go #[] tacticState script
  where
    go (script : Array Syntax.Tactic) (tacticState : TacticState) :
        StructuredScript → m (Array Syntax.Tactic × TacticState)
      | empty =>
        return (script, tacticState)
      | unstructuredStep ti tail => do
        let (script, tacticState) ← ti.render script tacticState
        go script tacticState tail
      | solve goal here tail => do
        let pos ← tacticState.getVisibleGoalIndex goal
        let (nestedScript, tacticState) ←
          tacticState.onGoalM goal λ ts => do
            let (nestedScript, nestedTacticState) ← go #[] ts here
            if ! nestedTacticState.hasNoVisibleGoals then
              throwError "expected script to solve the goal"
            pure (nestedScript, nestedTacticState)
        let t ←
          if pos == 0 then
            `(tactic| · $[$nestedScript:tactic]*)
          else
            let posLit := mkOneBasedNumLit pos
            `(tactic| on_goal $posLit:num => { $nestedScript:tactic* })
        go (script.push t) tacticState tail

-- TODO resolve positions as part of this step?
-- TODO We currently assume that we completely solve the tactic state. If we
-- don't, we have to allow getStep to fail and leave the goal alone.
partial def UnstructuredScript.toStructuredScript (tacticState : TacticState)
    (script : UnstructuredScript) : m StructuredScript := do
  let mut steps := {}
  for h : i in [:script.size] do
    let step := script[i]'h.2
    steps := steps.insert step.preGoal (i, step)
  (·.fst) <$> go steps tacticState
where
  go (steps : HashMap MVarId (Nat × TacticInvocation))
      (tacticState : TacticState) : m (StructuredScript × TacticState) := do
    if tacticState.hasNoVisibleGoals then
      return (.empty, tacticState)
    else if tacticState.hasSingleVisibleGoal ||
            tacticState.visibleGoalsHaveMVars then
      -- TODO If the original order happens to solve the main goal, we can
      -- structure opportunistically.
      let mut firstStep? := none
      for g in tacticState.visibleGoals do
        if let (some (i, step)) := steps[g.goal] then
          if let some (j, firstStep) := firstStep? then
            firstStep? := some $ if i < j then (i, step) else (j, firstStep)
          else
            firstStep? := some (i, step)
        else
          -- It's possible that a visible goal is solved as a side effect of
          -- some unrelated step. So we can't expect every visible goal to have
          -- an associated step.
          continue
      let some (_, firstStep) := firstStep?
        | throwError "internal error: found no step to solve any visible goal"
      let tacticState ← tacticState.applyTacticInvocation firstStep
      let (tailScript, tacticState) ← go steps tacticState
      return (.unstructuredStep firstStep tailScript, tacticState)
    else
      let mut tacticState := tacticState
      let mut nestedScripts := Array.mkEmpty tacticState.visibleGoals.size
      -- The following loop is not equivalent to a for loop because some of
      -- the later visible goals may be solved while solving an earlier visible
      -- goal.
      while h : tacticState.visibleGoals.size > 0 do
        let goal := tacticState.visibleGoals[0]
        let (nestedScript, nestedTacticState) ←
          tacticState.onGoalM goal.goal λ tacticState => go steps tacticState
        nestedScripts := nestedScripts.push (goal.goal, nestedScript)
        tacticState := nestedTacticState
      let script := nestedScripts.foldr (init := .empty)
        λ (goal, nestedScript) tail => .solve goal nestedScript tail
      return (script, tacticState)

end Aesop
