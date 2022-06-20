/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std

open Std (HashMap HashSet)

namespace Array

variable (α) [BEq α] [Hashable α]

private structure TopSortState where
  visited : HashSet α := {}
  result : Array (α × Array α)

private abbrev TopSortT m := StateT (TopSortState α) m

variable {α}

partial def topSortM [Monad m] (dependencies : α → m (Array α)) (as : Array α) :
    m (Array (α × Array α)) :=
  if as.isEmpty then
    return #[]
  else
    StateT.run' go { result := Array.mkEmpty as.size }
  where
    update (a : α) : TopSortT α m Unit :=
      unless (← MonadState.get).visited.contains a do
        let deps ← dependencies a
        _root_.modify λ s => { s with visited := s.visited.insert a }
        deps.forM $ update
        _root_.modify λ s => { s with result := s.result.push (a, deps) }

    go : TopSortT α m (Array (α × Array α)) := do
      as.forM $ update
      let s ← StateT.get
      return s.result

def topSort (dependencies : α → Array α) (as : Array α) : Array (α × Array α) :=
  Id.run $ topSortM dependencies as

end Array
