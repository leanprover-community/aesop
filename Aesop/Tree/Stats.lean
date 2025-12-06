/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Tree.Traversal
import Aesop.Tree.TreeM

namespace Aesop

def Goal.stats (g : Goal) : TreeM GoalStats := do
  let (goal, metaState) ← g.currentGoalAndMetaState (← getRootMetaState)
  let decl := metaState.meta.mctx.getDecl goal
  let lctxSize := decl.lctx.foldl (init := 0) fun acc ldecl =>
    if ldecl.isImplementationDetail then acc else acc + 1
  return {
    goalId := g.id.toNat
    goalKind := if g.isNormal then .postNorm else .preNorm
    forwardStateStats := g.forwardState.stats
    depth := g.depth
    lctxSize
  }

def collectGoalStatsIfEnabled : TreeM Unit := do
  if ← enableStats then
    let go : StateRefT (Array GoalStats) TreeM Unit :=
      postTraverseDown
        (fun gref => do
          let stats ← (← gref.get).stats
          modify (·.push stats))
        (fun _rref => return)
        (fun _cref => return)
        (.mvarCluster (← getThe Tree).root)
    let goalStats ← (·.2) <$> go.run #[]
    modifyStats ({ · with goalStats })

end Aesop
