/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.Step

open Lean Lean.Meta

namespace Aesop.Script

abbrev UScript := Array Step

variable [Monad m] [MonadError m] [MonadQuotation m] in
def UScript.render (tacticState : TacticState) (s : UScript) :
    m (Array Syntax.Tactic) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState := tacticState
  for step in s do
    let (script', tacticState') ← step.render script tacticState
    script := script'
    tacticState := tacticState'
  return script

def UScript.validate (s : UScript) : MetaM Unit :=
  s.forM (·.validate)

end Aesop.Script
