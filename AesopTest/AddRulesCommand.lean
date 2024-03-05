/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

-- Basic examples

structure TT₁ where

/-- error: tactic 'aesop' failed, made no progress -/
#guard_msgs in
example : TT₁ := by
  aesop

add_aesop_rules safe TT₁

example : TT₁ := by
  aesop

-- Local rules

structure TT₂ where

namespace Test

local add_aesop_rules safe TT₂

example : TT₂ := by
  aesop

end Test

/-- error: tactic 'aesop' failed, made no progress -/
#guard_msgs in
example : TT₂ := by
  aesop

-- Scoped rules

structure TT₃ where

namespace Test

scoped add_aesop_rules safe TT₃

example : TT₃ := by
  aesop

end Test

/-- error: tactic 'aesop' failed, made no progress -/
#guard_msgs in
example : TT₃ := by
  aesop

def Test.example : TT₃ := by
  aesop

-- Tactics

structure TT₄ where

/-- error: tactic 'aesop' failed, made no progress -/
#guard_msgs in
example : TT₄ := by
  aesop

add_aesop_rules safe (by exact TT₄.mk)

example : TT₄ := by
  aesop

-- Multiple rules

axiom T : Type
axiom U : Type
axiom f : T → U
axiom t : T

/-- error: tactic 'aesop' failed, made no progress -/
#guard_msgs in
example : U := by
  aesop

add_aesop_rules safe [(by apply f), t]

noncomputable example : U := by
  aesop
