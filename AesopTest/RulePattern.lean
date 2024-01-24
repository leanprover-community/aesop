/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

@[aesop safe forward (pattern := n + 1)]
axiom succ_pos (n : Nat) : 0 < n + 1

@[aesop safe forward (pattern := min x y)]
axiom foo {x y : Nat} : 0 < x → 0 < y → min x y ≤ x

axiom abs (n : Int) : Nat

notation "|" t "|" => abs t

@[aesop safe forward (pattern := |a + b|)]
axiom triangle (a b : Int) : |a + b| ≤ |a| + |b|
