/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

namespace Aesop

open Lean
open Std

/-
Invariant: between 0 and 0.1
-/
structure Percent where
  toFloat : Float
  deriving Inhabited, BEq

namespace Percent

protected def ofFloat (f : Float) : Option Percent :=
  if 0 <= f && f <= 1.0 then some ⟨f⟩ else none

instance : Mul Percent where
  mul p q := ⟨p.toFloat * q.toFloat⟩

instance : LT Percent where
  lt p q := p.toFloat < q.toFloat

instance : DecidableRel (α := Percent) (· < ·) :=
  λ p q => (inferInstance : Decidable (p.toFloat < q.toFloat))

instance : ToString Percent where
  toString p := toString p.toFloat

def hundred : Percent :=
  ⟨1⟩

def toHumanString (p : Percent) : String :=
  (toString (p.toFloat * 100) |>.takeWhile (· ≠ '.')) ++ "%"

protected def ofNat (n : Nat) : Option Percent :=
  Percent.ofFloat $ n.toFloat / 100

end Aesop.Percent
