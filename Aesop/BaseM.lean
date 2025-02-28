/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Stats.Basic
import Aesop.RulePattern.Cache

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- State of the `BaseM` monad. -/
structure BaseM.State where
  /-- The rule pattern cache. -/
  rulePatternCache : RulePatternCache
  /-- The RPINF cache. -/
  rpinfCache : RPINFCache
  /-- Stats collected during an Aesop call. -/
  stats : Stats
  deriving Inhabited

instance : EmptyCollection BaseM.State :=
  ⟨by refine' { .. } <;> exact ∅⟩

/-- Aesop's base monad. Contains no interesting data, only various caches and
stats. -/
abbrev BaseM := StateRefT BaseM.State MetaM

namespace BaseM

/-- Run a `BaseM` action. -/
protected def run (x : BaseM α) : MetaM α :=
  StateRefT'.run' x ∅

instance : MonadHashMapCacheAdapter Expr RulePatternCache.Entry BaseM where
  getCache := return (← get).rulePatternCache.map
  modifyCache f := modify λ s =>
    { s with rulePatternCache.map := f s.rulePatternCache.map }

instance : MonadHashMapCacheAdapter Expr RPINFRaw BaseM where
  getCache := return (← get).rpinfCache.map
  modifyCache f := modify λ s => { s with rpinfCache.map := f s.rpinfCache.map }

instance : MonadStats BaseM where
  modifyGetStats f := modifyGet λ s =>
    let (a, stats) := f s.stats
    (a, { s with stats })
  getStats := return (← get).stats
  modifyStats f := modify λ s => { s with stats := f s.stats }

instance : MonadBacktrack Meta.SavedState BaseM where
  saveState := Meta.saveState
  restoreState := (·.restore)

end Aesop.BaseM
