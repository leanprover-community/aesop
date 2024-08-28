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

abbrev StatsExtension := SimplePersistentEnvExtension StatsExtensionEntry Unit

def StatsExtension.importedEntries (env : Environment) (ext : StatsExtension) :
    Array (Array StatsExtensionEntry) :=
  ext.toEnvExtension.getState env |>.importedEntries

initialize statsExtension : StatsExtension ←
  registerSimplePersistentEnvExtension {
    addEntryFn := λ _ _ => ()
    addImportedFn := λ _ => ()
  }

def recordStatsIfEnabled [Monad m] [MonadEnv m] [MonadOptions m]
    (s : StatsExtensionEntry) : m Unit := do
  if ← isStatsCollectionEnabled then
    modifyEnv λ env => statsExtension.addEntry env s

abbrev StatsArray := Array StatsExtensionEntry

def mkStatsArray (localEntries : List StatsExtensionEntry)
    (importedEntries : Array (Array StatsExtensionEntry)) :
    StatsArray := Id.run do
  let mut result := #[]
  for entry in localEntries do
    result := result.push entry
  for entries in importedEntries do
    result := result ++ entries
  return result

def getStatsArray [Monad m] [MonadEnv m] : m StatsArray := do
  let env ← getEnv
  let current := statsExtension.getEntries env
  let imported := statsExtension.importedEntries env
  return mkStatsArray current imported

end Aesop
