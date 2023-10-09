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
theorem WalkingCospan_elim : WalkingCospan → Sum Empty Empty := id

example (h : WalkingCospan) : α := by
  aesop (add norm unfold [WidePullbackShape, WalkingCospan])

example (h : WalkingCospan) : α := by
  aesop (add norm simp [WidePullbackShape, WalkingCospan])
