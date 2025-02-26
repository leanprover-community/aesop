/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- Inspired by this Zulip discussion:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Goal.20state.20not.20updating.2C.20bugs.2C.20etc.2E/near/338356062

import Aesop

set_option aesop.check.all true

structure WalkingPair

def WidePullbackShape A B := Sum A B

abbrev WalkingCospan : Type := WidePullbackShape Empty Empty

@[aesop norm destruct]
def WalkingCospan_elim : WalkingCospan → Sum Empty Empty := id

/--
info: Try this:
  unfold WalkingCospan at h
  unfold WidePullbackShape at h
  cases h with
  | inl val =>
    have fwd : False := Aesop.BuiltinRules.empty_false val
    simp_all only
  | inr val_1 =>
    have fwd : False := Aesop.BuiltinRules.empty_false val_1
    simp_all only
-/
#guard_msgs in
example (h : WalkingCospan) : α := by
  aesop? (add norm unfold [WidePullbackShape, WalkingCospan])

example (h : WalkingCospan) : α := by
  aesop (add norm simp [WidePullbackShape, WalkingCospan])

@[aesop norm unfold]
def Foo := True

@[aesop norm unfold]
def Bar := False

/--
info: Try this:
  unfold Bar Foo
  unfold Foo at h₁
  unfold Foo Bar at h₂
  simp_all only
  cases h₂ with
  | inl val =>
    simp_all only
    apply PSum.inr
    simp_all only
  | inr val_1 => simp_all only
-/
#guard_msgs in
example (h₁ : Foo) (h₂ : PSum Foo Bar) : PSum Bar Foo := by
  aesop?
