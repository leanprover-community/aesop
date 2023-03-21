/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Tracing
import Aesop.Tree
import Aesop.Search.Queue.Class
import Std.Data.BinomialHeap

open Lean
open Std (BinomialHeap)

namespace Aesop.BestFirstQueue

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

protected def popGoal (q : BestFirstQueue) : Option GoalRef × BestFirstQueue :=
  match q.deleteMin with
  | none => (none, q)
  | some (ag, q) => (some ag.goal, q)

end BestFirstQueue

instance : Queue BestFirstQueue where
  init := return BestFirstQueue.init
  addGoals := BestFirstQueue.addGoals
  popGoal q := return BestFirstQueue.popGoal q


structure LIFOQueue where
  goals : Array GoalRef

namespace LIFOQueue

protected def init : LIFOQueue :=
  ⟨#[]⟩

protected def addGoals (q : LIFOQueue) (grefs : Array GoalRef) : LIFOQueue :=
  ⟨q.goals ++ grefs.reverse⟩

protected def popGoal (q : LIFOQueue) : Option GoalRef × LIFOQueue :=
  match q.goals.back? with
  | some g => (some g, ⟨q.goals.pop⟩)
  | none => (none, q)

instance : Queue LIFOQueue where
  init := return .init
  addGoals q grefs := return q.addGoals grefs
  popGoal q := return q.popGoal

end LIFOQueue


structure FIFOQueue where
  goals : Array GoalRef
  pos : Nat

namespace FIFOQueue

protected def init : FIFOQueue :=
  ⟨#[], 0⟩

protected def addGoals (q : FIFOQueue) (grefs : Array GoalRef) : FIFOQueue :=
  { q with goals := q.goals ++ grefs }

protected def popGoal (q : FIFOQueue) : Option GoalRef × FIFOQueue :=
  if h : q.pos < q.goals.size then
    (some q.goals[q.pos], { q with pos := q.pos + 1 })
  else
    (none, q)

instance : Queue FIFOQueue where
  init := return .init
  addGoals q grefs := return q.addGoals grefs
  popGoal q := return q.popGoal

end FIFOQueue

def Options.queue (opts : Aesop.Options) : Σ Q, Queue Q :=
  match opts.strategy with
  | .bestFirst => ⟨BestFirstQueue, inferInstance⟩
  | .depthFirst => ⟨LIFOQueue, inferInstance⟩
  | .breadthFirst => ⟨FIFOQueue, inferInstance⟩

end Aesop
