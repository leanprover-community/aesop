/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Meta

namespace Aesop

inductive SimpResult
  | solved
  | unchanged (newGoal : MVarId)
  | simplified (newGoal : MVarId)

namespace SimpResult

def newGoal? : SimpResult → Option MVarId
  | solved => none
  | unchanged g => some g
  | simplified g => some g

end SimpResult

structure SimpConfig extends Simp.ConfigCtx where
  maxDischargeDepth := 1
  useHyps := true

end Aesop
