/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tracing
import Aesop.Tree

open Lean
open Std (BinomialHeap)

namespace Aesop

class Queue (Q : Type) where
  init : BaseIO Q
  addGoals : Q → Array GoalRef → BaseIO Q
  popGoal : Q → BaseIO (Option GoalRef × Q)
  format : Q → MetaM MessageData

namespace Queue

def init' [Queue Q] (grefs : Array GoalRef) : BaseIO Q := do
  addGoals (← init) grefs

end Queue


namespace BestFirstQueue

structure ActiveGoal where
  goal : GoalRef
  priority : Percent
  lastExpandedInIteration : Iteration
    -- Iteration of the search loop when this goal was last expanded (counting
    -- from 1), or 0 if the goal was never expanded.
  addedInIteration : Iteration
    -- Iteration of the search loop when this goal was added. 0 for the root
    -- goal.

namespace ActiveGoal

-- We prioritise active goals lexicographically by the following criteria:
--
--  1. Goals with higher priority have priority.
--  2. Goals which were last expanded in an earlier iteration have priority.
--  3. Goals which were added in an earlier iteration have priority.
--
-- The last two criteria ensure a very weak form of fairness: if a search
-- produces infinitely many goals with the same success probability, each of
-- them will be expanded infinitely often.
--
-- Note that since we use a min-queue, `le x y` means `x` has priority over `y`.
protected def le (g h : ActiveGoal) : Bool :=
  g.priority > h.priority ||
    (g.priority == h.priority &&
      (g.lastExpandedInIteration ≤ h.lastExpandedInIteration ||
        (g.lastExpandedInIteration == h.lastExpandedInIteration &&
          g.addedInIteration ≤ h.addedInIteration)))

protected def ofGoalRef (gref : GoalRef) : BaseIO ActiveGoal := do
  let g ← gref.get
  return {
    goal := gref
    priority := g.priority
    lastExpandedInIteration := g.lastExpandedInIteration
    addedInIteration := g.addedInIteration
  }

end BestFirstQueue.ActiveGoal

def BestFirstQueue :=
  BinomialHeap BestFirstQueue.ActiveGoal BestFirstQueue.ActiveGoal.le

namespace BestFirstQueue

protected def init : BestFirstQueue :=
  BinomialHeap.empty

protected def addGoals (q : BestFirstQueue) (grefs : Array GoalRef) :
    BaseIO BestFirstQueue :=
  grefs.foldlM (init := q) λ q gref =>
    return q.insert (← ActiveGoal.ofGoalRef gref)

protected def popGoal (q : BestFirstQueue) : (Option GoalRef × BestFirstQueue) :=
  match q.deleteMin with
  | none => (none, q)
  | some (ag, q) => (some ag.goal, q)

protected def format (q : BestFirstQueue) : MetaM MessageData := do
  let traceMods ← TraceModifiers.get
  let goals ← q.toArray.mapM λ ag => do (← ag.goal.get).toMessageData traceMods
  return MessageData.node goals

end BestFirstQueue

instance : Queue BestFirstQueue where
  init := return BestFirstQueue.init
  addGoals := BestFirstQueue.addGoals
  popGoal q := return BestFirstQueue.popGoal q
  format := BestFirstQueue.format

end Aesop
