/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Aesop

structure LevelIndex where
  toNat : Nat
  deriving Inhabited, BEq, Hashable, DecidableEq, Ord

instance : LT LevelIndex where
  lt i j := i.toNat < j.toNat

instance : DecidableRel (α := LevelIndex) (· < ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat < j.toNat)

instance : LE LevelIndex where
  le i j := i.toNat ≤ j.toNat

instance : DecidableRel (α := LevelIndex) (· ≤ ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat ≤ j.toNat)

instance : ToString LevelIndex where
  toString i := toString i.toNat

end Aesop
