/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.Step

open Lean

namespace Aesop

abbrev ScriptT m := StateRefT' IO.RealWorld (Array Script.LazyStep) m

namespace ScriptT

protected def run [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : ScriptT m α) :
    m (α × Array Script.LazyStep) :=
  StateRefT'.run x #[]

end ScriptT

abbrev ScriptM := ScriptT MetaM

variable [MonadStateOf (Array Script.LazyStep) m]

def recordScriptStep (step : Script.LazyStep) : m Unit :=
  modify (·.push step)

def recordScriptSteps (steps : Array Script.LazyStep) : m Unit :=
  modify (· ++ steps)

end Aesop
