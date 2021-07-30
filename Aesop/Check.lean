/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean

namespace Aesop

def registerCheckOption [KVMap.Value α] (checkName : Name) (defValue : α)
    (descr : String) : IO (Lean.Option α) :=
  Option.register (`aesop.check ++ checkName)
    { defValue := defValue, group := "aesop", descr := descr }

initialize checkAllOption : Lean.Option Bool ←
  registerCheckOption `all false
    "(aesop) Enable all runtime checks. Individual checks can still be disabled."

initialize checkProofReconstructionOption : Lean.Option Bool ←
  registerCheckOption `proofReconstruction false
    "(aesop) Typecheck partial proof terms during proof reconstruction."

inductive Check
  | all
  | proofReconstruction

namespace Check

def toOption : Check → Lean.Option Bool
  | all => checkAllOption
  | proofReconstruction => checkProofReconstructionOption

def isEnabled [Monad m] [MonadOptions m] : Check → m Bool
  | all => return all.toOption.get (← getOptions)
  | c => do
    let opts ← getOptions
    match c.toOption.get? opts with
    | none => return all.toOption.get opts
    | some v => return v

end Check

end Aesop
