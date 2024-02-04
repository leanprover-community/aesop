/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import Std.Tactic.GuardMsgs

/--
error: duplicate rule name 'Nat.add_assoc'; rule name 'bar' was already specified
-/
#guard_msgs in
@[aesop norm simp Nat.add_assoc]
theorem bar : True := trivial
