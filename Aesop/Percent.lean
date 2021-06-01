/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean.Elab.Tactic.Basic

namespace Aesop

open Lean

/-
Invariant: between 0 and 100
-/
structure Percent where
  toNat : Nat

namespace Percent

protected def ofNat (n : Nat) : Option Percent :=
  if n <= 100 then some ⟨n⟩ else none

instance : Mul Percent where
  mul p q := ⟨Nat.max 1 ((p.toNat * q.toNat) / 100)⟩

instance : LT Percent where
  lt p q := p.toNat < q.toNat

instance : DecidableRel (α := Percent) (· < ·) :=
  λ p q => (inferInstance : Decidable (p.toNat < q.toNat))

protected def toString (p : Percent) : String :=
  toString p.toNat ++ "%"

instance : ToFormat Percent where
  format p := p.toString

-- TODO: parser for Percent?

end Percent
end Aesop