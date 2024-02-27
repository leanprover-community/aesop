/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Stats.Basic

open Lean

namespace Aesop

structure StatsExtensionEntry where
  /--
  The Aesop call for which stats were collected.
  -/
  aesopStx : Syntax
  /--
  The collected stats.
  -/
  stats : Stats

abbrev StatsArray := Array StatsExtensionEntry

structure StatsExtensionState where
  /--
  Entries for Aesop calls in the current module.
  -/
  currentEntries : List StatsExtensionEntry
  /--
  The size of `currentEntries`.
  -/
  currentEntriesSize : Nat
  /--
  Entries for Aesop calls in imported modules.
  -/
  importedEntries : Array (Array StatsExtensionEntry)
  deriving Inhabited

namespace StatsExtensionState

def toStatsArray (s : StatsExtensionState) : StatsArray := Id.run do
  let mut size := s.currentEntriesSize
  for entries in s.importedEntries do
    size := size + entries.size
  let mut result := Array.mkEmpty size
  for entry in s.currentEntries do
    result := result.push entry
  for entries in s.importedEntries do
    result := result ++ entries
  return result

protected def empty : StatsExtensionState where
  currentEntries := ∅
  currentEntriesSize := 0
  importedEntries := ∅

instance : EmptyCollection StatsExtensionState :=
  ⟨.empty⟩

end StatsExtensionState

abbrev StatsExtension :=
  PersistentEnvExtension StatsExtensionEntry StatsExtensionEntry
    StatsExtensionState

initialize statsExtension : StatsExtension ←
  registerPersistentEnvExtension {
    addEntryFn := λ state entry => { state with
      currentEntries := entry :: state.currentEntries
      currentEntriesSize := state.currentEntriesSize + 1
    }
    addImportedFn := λ importedEntries =>
      return { StatsExtensionState.empty with importedEntries }
    mkInitial := return ∅
    exportEntriesFn := λ state =>
      state.currentEntries.foldl (init := Array.mkEmpty state.currentEntriesSize)
        λ entries e => entries.push e
  }

def recordStatsIfEnabled [Monad m] [MonadEnv m] [MonadOptions m]
    (s : StatsExtensionEntry) : m Unit := do
  if ← isStatsCollectionEnabled then
    modifyEnv λ env => statsExtension.addEntry env s

def getStatsArray [Monad m] [MonadEnv m] : m StatsArray:= do
  return statsExtension.getState (← getEnv) |>.toStatsArray

end Aesop
