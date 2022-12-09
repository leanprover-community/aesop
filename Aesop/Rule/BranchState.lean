/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

structure RuleBranchState where
  numApplications : Nat
  deriving Inhabited, Repr

namespace RuleBranchState

protected def initial : RuleBranchState where
  numApplications := 0

instance : Std.ToFormat RuleBranchState where
  format := repr

end RuleBranchState
