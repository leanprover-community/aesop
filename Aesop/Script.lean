/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.PrettyPrinter

namespace Aesop

open Lean.Elab.Tactic in
-- FIXME remove
elab (name := Parser.onGoal) &"on_goal " n:num " => " ts:tacticSeq : tactic => do
  let gs := (← getGoals).toArray
  let n := n.getNat
  if n == 0 then
    throwError "on_goal: goal numbers start at 1, so 0 is not a valid goal number"
  if h : n - 1 < gs.size then
    let g := gs[n - 1]
    setGoals [g]
    evalTactic ts
    let gs := gs[:n - 1] ++ (← getUnsolvedGoals).toArray ++ gs[n:] -- FIXME off by one?
    setGoals gs.toList
  else
    throwError "on_goal: tried to select goal {n} but there are only {gs.size} goals"

-- FIXME move
open Lean.Elab.Tactic in
elab (name := Parser.solve) &"solve " ns:num+ " => " ts:tacticSeq : tactic => do
  let gs := (← getGoals).toArray
  let ns := ns.map (·.getNat) |>.qsortOrd
  let mut selectedGoals := Array.mkEmpty ns.size
  let mut otherGoals := Array.mkEmpty (gs.size - ns.size)
  let mut start := 0
  for n in ns do
    -- Note that `n` is a 1-based index into `gs`.
    if n == 0 then
      throwError "TODO"
    else if h : n - 1 < gs.size then
      selectedGoals := selectedGoals.push gs[n - 1]
      otherGoals := otherGoals ++ gs[start:n - 2].toArray -- TODO inefficient
      start := n
    else
      throwError "TODO"
  setGoals selectedGoals.toList
  evalTactic ts
  if ! (← getUnsolvedGoals).isEmpty then
    throwError "TODO"
  setGoals otherGoals.toList

-- FIXME move
syntax optTacticSeq := (tacticSeq)?

open Lean.Elab.Tactic in
/--
`[ts₁ | ts₂ | ... | tsₙ] executes the tactic sequence `ts₁` on the first
goal, `ts₂` on the second goal, etc. TODO describe corner cases
-/
elab (name := Parser.focusEach) "[" ts:sepBy(optTacticSeq, " | ") "]" : tactic => do
  let mut newGoals := #[]
  let ts : Array (TSyntax ``optTacticSeq) := ts
  let gs ← getGoals
  for t? in ts, g in gs do
    match t? with
    | `(optTacticSeq| $t:tacticSeq) =>
      setGoals [g]
      evalTactic t
      newGoals := newGoals ++ (← getUnsolvedGoals)
    | _ =>
      newGoals := newGoals.push g
  newGoals := newGoals ++ gs.drop ts.size
  setGoals newGoals.toList

example (h : A ∨ B) : B ∨ A := by
  cases h; [apply Or.inr; assumption | apply Or.inl; assumption]

example (h : A ∨ B) : B ∨ A := by
  cases h; [ | apply Or.inl]; [apply Or.inr; assumption | assumption]


-- FIXME move
macro &"unhygienic " t:tacticSeq : tactic =>
  `(tactic| set_option tactic.hygienic false in $t)


@[inline]
private def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1


/-
Invariant: goals occurring in `solvedGoals` do not occur in `goals`.
-/
structure TacticState where
  goals : Array MVarId -- TODO make this an UnorderedArraySet?
  solvedGoals : HashSet MVarId
  deriving Inhabited

namespace TacticState

variable [Monad m] [MonadError m]

@[inline]
def get? (tacticState : TacticState) (goal : MVarId) : Option Nat :=
  tacticState.goals.findIdx? (· == goal)

@[inline]
def get (tacticState : TacticState) (goal : MVarId) : m Nat := do
  if let (some idx) := tacticState.get? goal then
    return idx
  else
    throwError "goal {goal.name} is not in the tactic state"

@[inline]
def isEmpty (tacticState : TacticState) : Bool :=
  tacticState.goals.isEmpty

@[inline]
def ensureIsEmpty (tacticState : TacticState) : m Unit := do
  if ! tacticState.isEmpty then
    throwError "expected there to be no remaining goals"

def empty : TacticState where
  goals := #[]
  solvedGoals := {}

def initial (goals : Array MVarId) : TacticState where
  goals := goals
  solvedGoals := {}

instance : EmptyCollection TacticState :=
  ⟨empty⟩

def singleton (goal : MVarId) : TacticState where
  goals := #[goal]
  solvedGoals := {}

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

def applyTactic (tacticState : TacticState) (inGoal : MVarId)
    (outGoals : Array MVarId) (otherSolvedGoals : Array MVarId) :
    m TacticState := do
  let (some goals) := replaceWithArray tacticState.goals inGoal outGoals
    | throwError "goal {inGoal.name} is not in the tactic state"
  let solvedGoals := tacticState.solvedGoals.insertMany otherSolvedGoals
  let goals := goals.filter (! solvedGoals.contains ·)
  return { goals, solvedGoals }

def restrict (tacticState : TacticState) (goals : Array MVarId) :
    m TacticState := do
  let mut tacticState := tacticState
  for goal in goals do
    let idx ← tacticState.get goal
    tacticState := { tacticState with goals := tacticState.goals.eraseIdx idx }
  return tacticState

def eraseGoals (tacticState : TacticState) (goals : HashSet MVarId) :
    TacticState :=
  { tacticState with goals := tacticState.goals.filter (! goals.contains ·)  }

end TacticState


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
def focusAndDoneEach (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  bs.mapM λ b => do `(tactic| { $(← b.run):tactic* })

@[inline]
def focusEach (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  if bs.size == 0 then
    return #[]
  let ts ← bs.mapM (·.run)
  if ts.all (·.isEmpty) then
    return #[]
  if h : ts.size = 1 then
    let t := ts[0]'(by simp [h])
    return #[← `(tactic| focus $t:tactic*)]
  else
    let ts ← ts.mapM λ (t : Array Syntax.Tactic) =>
      if t.isEmpty then
        `(optTacticSeq| )
      else
        `(optTacticSeq| $t:tactic*)
    return #[← `(tactic| [ $[$ts]|* ])]

@[inline]
def seq (b₁ b₂ : UnstructuredScriptBuilder m) : UnstructuredScriptBuilder m :=
  return (← b₁.run) ++ (← b₂.run)

@[inline]
def seqFocusEach (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) : UnstructuredScriptBuilder m :=
  b.seq (.focusEach bs)

@[inline]
def seqFocusAndDoneEach (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) : UnstructuredScriptBuilder m :=
  b.seq (.focusAndDoneEach bs)

@[inline]
protected def id : UnstructuredScriptBuilder m :=
  return #[]

instance [Pure m] : Inhabited (UnstructuredScriptBuilder m) :=
  ⟨pure #[]⟩

@[inline]
def error [MonadError m] (e : MessageData) : UnstructuredScriptBuilder m :=
  throwError e

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
      UnstructuredScriptBuilder.ofTactics ts |>.seqFocusAndDoneEach conts

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
        let b'Conts := conts[start:«end»] -- FIXME off by one?
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

def error (msg : MessageData) : ScriptBuilder m where
  unstructured := .error msg
  structured := .error msg

def seq (b : ScriptBuilder m) (bs : Array (ScriptBuilder m)) :
    ScriptBuilder m where
  unstructured := b.unstructured.seqFocusEach $ bs.map (·.unstructured)
  structured := b.structured.seq $ bs.map (·.structured)

def unknown (tactic : Name) : ScriptBuilder m :=
  .error m!"Don't know how to build syntax for tactic '{tactic}'"

def assertHypotheses (goal : MVarId) (hs : Array Hypothesis) :
    ScriptBuilder MetaM :=
  .ofTactics 1 $ goal.withContext $ hs.mapM λ h => do
    `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))

def clear (goal : MVarId) (fvarIds : Array FVarId) :
    ScriptBuilder MetaM :=
  .ofTactic 1 $ goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    `(tactic| clear $userNames*)

def cases (goal : MVarId) (fvarId : FVarId) (subgoals : Nat) :
    ScriptBuilder MetaM :=
  .ofTactic subgoals $ goal.withContext do
    `(tactic| unhygienic cases $(mkIdent $ ← fvarId.getUserName):ident)

end ScriptBuilder

abbrev RuleTacScriptBuilder := ScriptBuilder MetaM


def _root_.Lean.MVarId.assertHypothesesWithSyntax (goal : MVarId)
    (hs : Array Hypothesis) :
    MetaM (Array FVarId × MVarId × ScriptBuilder MetaM) := do
  let (fvarIds, goal') ← goal.assertHypotheses hs
  return (fvarIds, goal', .assertHypotheses goal hs)

def _root_.Lean.MVarId.clearWithSyntax (goal : MVarId) (fvarId : FVarId) :
    MetaM (MVarId × ScriptBuilder MetaM) :=
  return (← goal.clear fvarId, .clear goal #[fvarId])

def _root_.Lean.MVarId.tryClearWithSyntax (goal : MVarId) (fvarId : FVarId) :
    MetaM (MVarId × ScriptBuilder MetaM) := do
  let goal' ← goal.tryClear fvarId
  if goal' == goal then
    return (goal', .id)
  else
    return (goal', .clear goal #[fvarId])

def _root_.Lean.MVarId.tryClearManyWithSyntax (goal : MVarId)
    (fvarIds : Array FVarId) :
    MetaM (MVarId × Array FVarId × ScriptBuilder MetaM) := do
  let (goal', cleared) ← goal.tryClearMany' fvarIds
  return (goal', cleared, .clear goal cleared)

def _root_.Lean.MVarId.casesWithSyntax (goal : MVarId) (fvarId : FVarId) :
    MetaM (Array CasesSubgoal × ScriptBuilder MetaM) := do
  let goals ← goal.cases fvarId
  return (goals, .cases goal fvarId goals.size)


-- FIXME remove
-- set_option linter.unusedVariables false in
-- mutual
--   inductive StructuredScript m
--     | empty
--     | seq (t : StructuredScriptBuilder m) (ss : Array (StructuredScript m))
--     | seqUnstructured (goals : Array MVarId) (s : UnstructuredScript m)

--   inductive UnstructuredScript m
--     | empty
--     | seq (inGoal : MVarId) (t : UnstructuredScriptBuilder m)
--         (outGoals : Array MVarId) (otherClosedGoals : Array MVarId)
--         (s : UnstructuredScript m)
--     | seqStructured (s : StructuredScript m)
-- end

-- mutual
--   -- TODO reverse array to go fast?
--   partial def StructuredScript.render :
--       StructuredScript m → UnstructuredScriptBuilder m
--     | .empty => return #[]
--     | .seq t ss =>
--       t.elim $ ss.map (·.render) |>.toSubarray
--     | .seqUnstructured goals s =>
--       s.render ⟨goals⟩

--   partial def UnstructuredScript.render (goalPosMap : TacticState) :
--       UnstructuredScript m → m (Array Syntax.Tactic)
--     | .empty => return #[]
--     | .seq inGoal t outGoals otherSolvedGoals s => do
--       let (some pos) := goalPosMap.get? inGoal | throwError
--         "position of goal {inGoal.name} is unknown"
--       let t ← `(tactic|
--         on_goal $(Syntax.mkNumLit $ toString pos) => $(← t.run):tactic*)
--       let (goalsPZ) := goalPosMap.applyTactic inGoal outGoals otherClosedGoals
--       let ts ← s.render goalPosMap
--       return #[t] ++ ts
--     | .seqStructured s => s.render
-- end

structure UnstructuredScriptStep where
  tacticSeq : Array Syntax.Tactic
  inGoal : MVarId
  outGoals : Array MVarId
  otherSolvedGoals : Array MVarId
  deriving Repr

def UnstructuredScriptStep.dummy (inGoal outGoal : MVarId) :
    UnstructuredScriptStep where
  tacticSeq := #[]
  inGoal := inGoal
  outGoals := #[outGoal]
  otherSolvedGoals := #[]

def TacticState.applyUnstructuredScriptStep (tacticState : TacticState)
    (step : UnstructuredScriptStep) : m TacticState :=
  tacticState.applyTactic step.inGoal step.outGoals step.otherSolvedGoals

abbrev UnstructuredScript := Array UnstructuredScriptStep

def UnstructuredScript.render (initialGoals : Array MVarId)
    (s : UnstructuredScript) : m (Array Syntax.Tactic) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState : TacticState :=
    { goals := initialGoals, solvedGoals := {} }
  for step in s do
    if step.tacticSeq.size == 0 then
      tacticState ← tacticState.applyUnstructuredScriptStep step
    else
      let pos := mkOneBasedNumLit $ ← tacticState.get step.inGoal
      let t ← `(tactic| on_goal $pos:num => $(step.tacticSeq):tactic*)
      script := script.push t
      tacticState ← tacticState.applyUnstructuredScriptStep step
  return script


inductive Script
  | empty
  | seq (s₁ s₂ : Script)
  | onGoal (ts : Array Syntax.Tactic) (inGoal : MVarId)
      (outGoals : Array MVarId) (otherSolvedGoals : Array MVarId)
  | solveEach (ss : Array (MVarId × Script))
  | solveSubset (mvarIds : Array MVarId) (s : Script)
  deriving Inhabited

partial def Script.render (initialGoals : Array MVarId) (s : Script) :
    m (Array Syntax.Tactic) :=
  (·.fst) <$> go #[] { goals := initialGoals, solvedGoals := {} } s
  where
    go (acc : Array Syntax.Tactic) (tacticState : TacticState) :
        Script → m (Array Syntax.Tactic × TacticState)
      | empty => return (#[], tacticState)
      | seq s₁ s₂ => do
        let (acc, tacticState) ← go acc tacticState s₁
        go acc tacticState s₂
      | onGoal ts inGoal outGoals otherSolvedGoals => do
        let pos := mkOneBasedNumLit (← tacticState.get inGoal)
        let t ← `(tactic| on_goal $pos:num => $ts:tactic*)
        let tacticState ←
          tacticState.applyTactic inGoal outGoals otherSolvedGoals
        return (acc.push t, tacticState)
      | solveEach ss => do
        let ss ← ss.mapM λ (mvarId, s) =>
          return (mvarId, ← tacticState.get mvarId, s)
        let ss := ss.qsort (λ (_, pos₁, _) (_, pos₂, _) => pos₁ < pos₂)
        let mut acc := acc
        let mut tacticState := tacticState
        let useBraces := isCompleteAscendingSequence ss (λ (_, pos, _) => pos)
        for (mvarId, pos, s) in ss do
          let (nestedTactics, nestedTacticState) ← go #[] (.singleton mvarId) s
          nestedTacticState.ensureIsEmpty
          tacticState :=
            tacticState.eraseGoals $ nestedTacticState.solvedGoals.insert mvarId
          let t ←
            if useBraces then
              `(tactic| { $nestedTactics:tactic* })
            else
              `(tactic| solve $(mkOneBasedNumLit pos) => $nestedTactics:tactic*)
          acc := acc.push t
        tacticState.ensureIsEmpty
        return (acc, tacticState)
      | solveSubset mvarIds s => do
        let poss ← mvarIds.mapM (mkOneBasedNumLit <$> tacticState.get ·)
        let (ts, nestedTacticState) ←
          go #[] (← tacticState.restrict mvarIds) s
        nestedTacticState.ensureIsEmpty
        let t ← `(tactic| solve $poss:num* => $ts:tactic*)
        let tacticState :=
          tacticState.eraseGoals $
            nestedTacticState.solvedGoals.insertMany mvarIds
        return (acc.push t, tacticState)

    isCompleteAscendingSequence {α} (xs : Array α) (f : α → Nat) :
        Bool := Id.run do
      for h : i in [:xs.size] do
        if i != f (xs[i]'h.2) then
          return false
      return true


-- FIXME remove
-- structure ScriptStep (m) where
--   unstructuredScriptBuilder : UnstructuredScriptBuilder m
--   structuredScriptBuilder : StructuredScriptBuilder m
--   inGoal : MVarId
--   outGoals : Array MVarId
--   otherSolvedGoals : Array MVarId

-- @[inline]
-- def TacticState.applyScriptStep (tacticState : TacticState) (step : ScriptStep m) :
--     (TacticState × Array MVarId) :=
--   tacticState.applyTactic step.inGoal step.outGoals step.otherSolvedGoals

-- structure Script' (m) where
--   steps : Array (ScriptStep m)

-- namespace Script'

-- def renderUnstructured (initialGoals : Array MVarId) (script : Script' m) :
--     m (Array Syntax.Tactic) := do
--   let mut res := Array.mkEmpty script.steps.size
--   let mut tacticState : TacticState := ⟨initialGoals⟩
--   for step in script.steps do
--     let (some pos) := tacticState.get? step.inGoal | throwError
--       "position of goal {step.inGoal.name} is unknown"
--     let tac ← step.unstructuredScriptBuilder
--     let onGoal ←
--       `(tactic| on_goal $(Syntax.mkNumLit $ toString pos) => $tac:tactic*)
--     res := res.push onGoal
--     tacticState := tacticState.applyScriptStep step
--   return res

-- end Script'

end Aesop
