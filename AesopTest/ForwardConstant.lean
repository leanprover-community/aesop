/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

structure Foo where
  foo ::

/--
error: tactic 'aesop' failed, made no progress
-/
#guard_msgs in
example : Foo := by
  aesop

example : Foo := by
  aesop (add safe forward Foo.foo)
