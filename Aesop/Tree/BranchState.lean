/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop.Rule.Basic

open Lean
open Std (PersistentHashMap)

namespace Aesop

def BranchState := PersistentHashMap RuleName RuleBranchState

namespace BranchState

instance : Inhabited BranchState :=
  inferInstanceAs $ Inhabited (PersistentHashMap _ _)

protected def empty : BranchState :=
  {}

def find? (r : Rule α) (bs : BranchState) : Option RuleBranchState :=
  if r.usesBranchState then PersistentHashMap.find? bs r.name else none

def insert (r : Rule α) (rbs : RuleBranchState) (bs : BranchState) :
    BranchState :=
  if r.usesBranchState then PersistentHashMap.insert bs r.name rbs else bs

def update (r : Rule α) (rbs : Option RuleBranchState) (bs : BranchState) :
    BranchState :=
  if r.usesBranchState then
    match rbs with
    | none => bs
    | some rbs => PersistentHashMap.insert bs r.name rbs
  else
    bs

end BranchState

end Aesop
