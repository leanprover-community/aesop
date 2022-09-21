/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
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
