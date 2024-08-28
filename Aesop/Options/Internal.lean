/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Check
import Aesop.Options.Public

open Lean
open Lean.Meta

namespace Aesop

structure Options' extends Options where
  generateScript : Bool
  forwardMaxDepth? : Option Nat
  deriving Inhabited

def Options.toOptions' [Monad m] [MonadOptions m] (opts : Options)
    (forwardMaxDepth? : Option Nat := none) : m Options' := do
  let generateScript ←
    pure (aesop.dev.generateScript.get (← getOptions)) <||>
    pure opts.traceScript <||>
    Check.script.isEnabled <||>
    Check.script.steps.isEnabled
  return { opts with generateScript, forwardMaxDepth? }

end Aesop
