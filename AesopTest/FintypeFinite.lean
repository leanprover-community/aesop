import Aesop

/-
Error coming from ` Matrix.Nondegenerate.toLinearMap₂` caused by
the relation of `[Finite α]` and `[Fintype α]` in Mathlib4. -/

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def myDef (α : Type) : Type := sorry

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry' -/
#guard_msgs in
class myInst1 (α : Type) where
  elems : Type := sorry
  prop : True := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
class myInst2 (α : Type) : Prop where
  prop : True := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
instance (α : Type) [myInst1 α] : myInst2 α := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
instance (α : Type) [myInst2 α] : myInst1 α := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def myProp {α : Type} [myInst2 α] (m : myDef α): Prop := sorry

/--
warning: declaration uses 'sorry' -/
#guard_msgs in
def myThm (α R : Type) [myInst1 α] (m : myDef α) (h : myProp m) : False := sorry

/--
error: saturate: internal error: aesop: internal error: matchPremise?:
while matching hyp _uniq.226: no assignment for variable 2 -/
#guard_msgs in
example (α : Type) [myInst1 α] (m : myDef α) (h : myProp m) : False := by
  saturate [myThm]
