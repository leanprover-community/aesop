/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule.Basic

open Lean
open Std (PersistentHashMap)

namespace Aesop

def BranchState := PersistentHashMap Name RuleBranchState

namespace BranchState

instance : Inhabited BranchState :=
  inferInstanceAs $ Inhabited (PersistentHashMap _ _)

protected def empty : BranchState :=
  {}

def find? (r : Rule' α τ) (bs : BranchState) : Option RuleBranchState :=
  if r.usesBranchState then PersistentHashMap.find? bs r.name else none

def insert (r : Rule' α τ) (rbs : RuleBranchState) (bs : BranchState) :
    BranchState :=
  PersistentHashMap.insert bs r.name rbs

def update (r : Rule' α τ) (rbs : Option RuleBranchState) (bs : BranchState) :
    BranchState :=
  match rbs with
  | none => bs
  | some rbs => bs.insert r rbs

end BranchState

end Aesop
