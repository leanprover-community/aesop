/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

axiom P : Prop
axiom T : Prop
axiom Q : Nat → Prop
axiom R : Nat → Prop
axiom S : Nat → Prop

@[aesop safe]
axiom q_r_p : ∀ x, Q x → R x → P

@[aesop safe]
axiom s_q : ∀ x y, S y → Q x

@[aesop safe]
axiom s_r : ∀ x y, S y → R x

axiom s : S 0

example : P := by
  aesop
