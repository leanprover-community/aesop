/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Stats.Basic
import Lean.Data.Position

open Lean Lean.Elab

namespace Aesop

structure StatsFileRecord extends Stats where
  file : String
  position : Option Position
  declaration : Option Name
  goalSolved : Bool
  deriving ToJson

namespace StatsFileRecord

variable [Monad m] [MonadLog m] [MonadParentDecl m] in
protected def ofStats (aesopStx : Syntax) (goalSolved : Bool) (stats : Stats) :
    m StatsFileRecord := do
  let file ← getFileName
  let fileMap ← getFileMap
  let position := aesopStx.getPos?.map fileMap.toPosition
  let declaration ← getParentDeclName?
  return { stats with file, position, declaration, goalSolved }

end StatsFileRecord

variable [Monad m] [MonadLog m] [MonadOptions m] [MonadParentDecl m] [MonadLiftT IO m] in
def appendStatsToStatsFileIfEnabled (aesopStx : Syntax) (stats : Stats)
    (allGoalsSolved : Bool) : m Unit := do
  let file := aesop.stats.file.get (← getOptions)
  if file == "" then
    return
  let record ← StatsFileRecord.ofStats aesopStx allGoalsSolved stats
  IO.FS.withFile file .append fun hdl => do
    -- Append mode atomically moves the cursor to EOF on write, so there is no
    -- race condition between locking the file and moving to EOF.
    hdl.lock (exclusive := true)
    try
      hdl.putStrLn <| toJson record |>.compress
    finally
      hdl.unlock

end Aesop
