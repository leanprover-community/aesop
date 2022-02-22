/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

namespace Aesop

open Lean
open Std

/-
Invariant: between 0 and 1.0
-/
structure Percent where
  toFloat : Float
  deriving Inhabited

namespace Percent

protected def ofFloat (f : Float) : Option Percent :=
  if 0 <= f && f <= 1.0 then some ⟨f⟩ else none

instance : Mul Percent where
  mul p q := ⟨p.toFloat * q.toFloat⟩

@[inline]
def δ : Percent :=
  ⟨0.00001⟩

instance : BEq Percent where
  beq | ⟨p⟩, ⟨q⟩ => if p > q then p - q < δ.toFloat else q - p < δ.toFloat

instance : Ord Percent where
  compare p q :=
    if p == q then Ordering.eq
    else if p.toFloat < q.toFloat then Ordering.lt
    else Ordering.gt

-- NOTE: This is not the same as
--
--     p < q := p.toFloat < q.toFloat
--
-- That definition would not agree with the Ord instance.
instance : LT Percent :=
  ltOfOrd

instance : LE Percent :=
  leOfOrd

instance : ToString Percent where
  toString p := toString p.toFloat

instance : HPow Percent Nat Percent where
  hPow | ⟨p⟩, n => ⟨p ^ n.toFloat⟩

def ninety : Percent :=
  ⟨0.9⟩

def hundred : Percent :=
  ⟨1⟩

def toHumanString (p : Percent) : String :=
  let str := toString (p.toFloat * 100)
  match str.split λ c => c == '.' with
  | [beforePoint] => beforePoint ++ "%"
  | [beforePoint, afterPoint] =>
    beforePoint ++ "." ++ afterPoint.take 4 ++ "%"
  | _ => "ERROR%"

protected def ofNat (n : Nat) : Option Percent :=
  Percent.ofFloat $ n.toFloat / 100

end Aesop.Percent
