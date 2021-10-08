/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean

namespace Aesop

def registerCheckOption (checkName : Name) (defValue : Bool)
    (descr : String) : IO (Lean.Option Bool) :=
  Option.register (`aesop.check ++ checkName)
    { defValue := defValue, group := "aesop", descr := descr }

initialize checkAllOption : Lean.Option Bool ←
  registerCheckOption `all false
    "(aesop) Enable all runtime checks. Individual checks can still be disabled."

initialize checkProofReconstructionOption : Lean.Option Bool ←
  registerCheckOption `proofReconstruction false
    "(aesop) Typecheck partial proof terms during proof reconstruction."

initialize checkTreeOption : Lean.Option Bool ←
  registerCheckOption `tree false
    "(aesop) Check search tree invariants after every iteration of the search loop. Very expensive."

initialize checkUnificationGoalAssignmentsOption : Lean.Option Bool ←
  registerCheckOption `unificationGoalAssignments false
    "(aesop) Typecheck assignments to unification goal metavariables."

initialize checkRules : Lean.Option Bool ←
  registerCheckOption `rules false
    "(aesop) Check that information reported by rules is correct."

inductive Check
  | all
  | tree
  | proofReconstruction
  | unificationGoalAssignments
  | rules

namespace Check

@[inlineIfReduce]
def toOption : Check → Lean.Option Bool
  | all => checkAllOption
  | tree => checkTreeOption
  | proofReconstruction => checkProofReconstructionOption
  | unificationGoalAssignments => checkUnificationGoalAssignmentsOption
  | rules => checkRules

def isEnabled [Monad m] [MonadOptions m] : Check → m Bool
  | all => return all.toOption.get (← getOptions)
  | c => do
    let opts ← getOptions
    match c.toOption.get? opts with
    | none => return all.toOption.get opts
    | some v => return v

def name (c : Check) : Name := c.toOption.name

end Check

end Aesop
