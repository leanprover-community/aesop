/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

-- We forbid `unfold` rules for recursive functions since they would lead to
-- infinite unfolding.

@[aesop norm unfold]
def f₁ : Nat → Nat :=
  λ _ => 0

@[aesop norm unfold]
def f₂ : Nat → Nat
  | 0 => 0
  | n + 1 => f₂ n

@[aesop norm unfold]
def f₃ : Nat → Nat :=
  λ n =>
    match n with
    | 0 => 0
    | n + 1 => f₃ n

@[aesop norm unfold]
def f₄ : Nat → Nat
  | 0 => 0
  | n + 1 => f₄ n

-- A limitation of our approach to checking for recursive `unfold` rules:
-- mutually recursive rules are not detected. But that's probably fine in
-- practice.

mutual
  @[aesop norm unfold]
  def f₅ : Nat → Nat
    | 0 => 0
    | n + 1 => f₆ n

  @[aesop norm unfold]
  def f₆ : Nat → Nat
    | 0 => 0
    | n + 1 => f₅ n
end

-- We also forbid `unfold` rules for declarations that don't unfold.

@[aesop norm unfold]
axiom test : Nat
