/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Aesop

inductive SNat where
  | zero
  | succ (n : SNat)

def Nat.toSNat : Nat → SNat
  | zero => .zero
  | succ n => .succ n.toSNat

open Lean Lean.Meta Lean.Elab.Term in
elab "snat%" n:num : term => do
  let n ← elabTerm n (some $ .const ``Nat [])
  reduceAll (.app (.const ``Nat.toSNat []) n)

example (P : SNat → Prop) (h : P (snat% 50)) : True :=
  trivial
