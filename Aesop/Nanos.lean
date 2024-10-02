/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Aesop

structure Nanos where
  nanos : Nat
  deriving Inhabited, BEq, Ord

namespace Nanos

instance : OfNat Nanos n where
  ofNat := ⟨n⟩

instance : LT Nanos where
  lt | ⟨n₁⟩, ⟨n₂⟩ => n₁ < n₂

instance : DecidableRel (α := Nanos) (· < ·) :=
  λ ⟨n₁⟩ ⟨n₂⟩ => inferInstanceAs (Decidable (n₁ < n₂))

instance : LE Nanos where
  le | ⟨n₁⟩, ⟨n₂⟩ => n₁ ≤ n₂

instance : DecidableRel (α := Nanos) (· ≤ ·) :=
  λ ⟨n₁⟩ ⟨n₂⟩ => inferInstanceAs (Decidable (n₁ ≤ n₂))

instance : Add Nanos where
  add n m := ⟨n.nanos + m.nanos⟩

instance : HDiv Nanos Nat Nanos where
  hDiv n m := ⟨n.nanos / m⟩

def printAsMillis (n : Nanos) : String :=
  let str := toString (n.nanos.toFloat / 1000000)
  match str.split λ c => c == '.' with
  | [beforePoint] => beforePoint ++ "ms"
  | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 1 ++ "ms"
  | _ => unreachable!

end Aesop.Nanos
