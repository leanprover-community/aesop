/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Aesop

structure SlotIndex where
  toNat : Nat
  deriving Inhabited, BEq, Hashable, DecidableEq, Ord

instance : LT SlotIndex where
  lt i j := i.toNat < j.toNat

instance : DecidableRel (α := SlotIndex) (· < ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat < j.toNat)

instance : LE SlotIndex where
  le i j := i.toNat ≤ j.toNat

instance : DecidableRel (α := SlotIndex) (· ≤ ·) :=
  λ i j => inferInstanceAs $ Decidable (i.toNat ≤ j.toNat)

instance : HAdd SlotIndex Nat SlotIndex where
  hAdd i j := ⟨i.toNat + j⟩

instance : HSub SlotIndex Nat SlotIndex where
  hSub i j := ⟨i.toNat - j⟩

instance : ToString SlotIndex where
  toString i := toString i.toNat

end Aesop
