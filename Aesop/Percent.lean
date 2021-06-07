/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean.Elab.Tactic.Basic

namespace Aesop

open Lean

/-
Invariant: between 0 and 0.1
-/
structure Percent where
  toFloat : Float
  deriving Inhabited

namespace Percent

protected def ofFloat (f : Float) : Option Percent :=
  if 0 <= f && f <= 1.0 then some ⟨f⟩ else none

instance : Mul Percent where
  mul p q := ⟨p.toFloat * q.toFloat⟩

instance : LT Percent where
  lt p q := p.toFloat < q.toFloat

instance : DecidableRel (α := Percent) (· < ·) :=
  λ p q => (inferInstance : Decidable (p.toFloat < q.toFloat))

instance : ToFormat Percent where
  format p := toString p.toFloat

def hundred : Percent :=
  ⟨1⟩

-- TODO: parser for Percent?

end Percent
end Aesop
