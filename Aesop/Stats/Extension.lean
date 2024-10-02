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
  /-
  The file in which Aesop was called.
  -/
  fileName : String
  /-
  The position in the file where Aesop was called.
  -/
  position? : Option Position
  /--
  The collected stats.
  -/
  stats : Stats

namespace StatsExtensionEntry

def forCurrentFile [Monad m] [MonadLog m] (stx : Syntax) (stats : Stats) :
    m StatsExtensionEntry := do
  let fileName ← getFileName
  let fileMap ← getFileMap
  let position? := stx.getPos?.map fileMap.toPosition
  return { aesopStx := stx, stats, fileName, position? }

end StatsExtensionEntry

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

def recordStatsForCurrentFileIfEnabled [Monad m] [MonadEnv m] [MonadOptions m]
    [MonadLog m] (aesopStx : Syntax) (stats : Stats) : m Unit := do
  if ← isStatsCollectionEnabled then
    let entry ← StatsExtensionEntry.forCurrentFile aesopStx stats
    modifyEnv λ env => statsExtension.addEntry env entry

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
