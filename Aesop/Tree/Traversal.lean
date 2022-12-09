/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tree.Data

namespace Aesop

inductive TreeRef
  | goal (gref : GoalRef)
  | rapp (rref : RappRef)
  | mvarCluster (cref : MVarClusterRef)

section

open TreeRef

variable
  {m} [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (visitGoalPre : GoalRef → m Bool)
  (visitGoalPost : GoalRef → m Unit)
  (visitRappPre : RappRef → m Bool)
  (visitRappPost : RappRef → m Unit)
  (visitMVarClusterPre : MVarClusterRef → m Bool)
  (visitMVarClusterPost : MVarClusterRef → m Unit)

@[specialize]
partial def traverseDown : TreeRef → m Unit
  | goal gref => do
    if ← visitGoalPre gref then
      (← gref.get).children.forM (traverseDown ∘ rapp)
      visitGoalPost gref
  | rapp rref => do
    if ← visitRappPre rref then
      (← rref.get).children.forM (traverseDown ∘ mvarCluster)
      visitRappPost rref
  | mvarCluster cref => do
    if ← visitMVarClusterPre cref then
      (← cref.get).goals.forM (traverseDown ∘ goal)
      visitMVarClusterPost cref

@[specialize]
partial def traverseUp : TreeRef → m Unit
  | goal gref => do
    if ← visitGoalPre gref then
      traverseUp $ mvarCluster (← gref.get).parent
      visitGoalPost gref
  | rapp rref => do
    if ← visitRappPre rref then
      traverseUp $ goal (← rref.get).parent
      visitRappPost rref
  | mvarCluster cref => do
    if ← visitMVarClusterPre cref then
      if let (some parent) := (← cref.get).parent? then
        traverseUp $ rapp parent
      visitMVarClusterPost cref

end

@[inline]
def preTraverseDown [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (visitGoal : GoalRef → m Bool) (visitRapp : RappRef → m Bool)
  (visitMVarCluster : MVarClusterRef → m Bool) : TreeRef → m Unit :=
  traverseDown
    visitGoal
    (λ _ => pure ())
    visitRapp
    (λ _ => pure ())
    visitMVarCluster
    (λ _ => pure ())

@[inline]
def preTraverseUp [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (visitGoal : GoalRef → m Bool) (visitRapp : RappRef → m Bool)
  (visitMVarCluster : MVarClusterRef → m Bool) : TreeRef → m Unit :=
  traverseUp
    visitGoal
    (λ _ => pure ())
    visitRapp
    (λ _ => pure ())
    visitMVarCluster
    (λ _ => pure ())

@[inline]
def postTraverseDown [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (visitGoal : GoalRef → m Unit) (visitRapp : RappRef → m Unit)
  (visitMVarCluster : MVarClusterRef → m Unit) : TreeRef → m Unit :=
  traverseDown
    (λ _ => pure true)
    visitGoal
    (λ _ => pure true)
    visitRapp
    (λ _ => pure true)
    visitMVarCluster

@[inline]
def postTraverseUp [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (visitGoal : GoalRef → m Unit) (visitRapp : RappRef → m Unit)
  (visitMVarCluster : MVarClusterRef → m Unit) : TreeRef → m Unit :=
  traverseUp
    (λ _ => pure true)
    visitGoal
    (λ _ => pure true)
    visitRapp
    (λ _ => pure true)
    visitMVarCluster

end Aesop
