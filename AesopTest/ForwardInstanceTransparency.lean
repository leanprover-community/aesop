import Aesop

-- This test case was the motivation for switching the transparency at which forward
-- reasoning operates from `reducible` to `instances`.

def PNat := { n : Nat // 0 < n }

class AddCommMagma (α : Type u) extends Add α where
  add_comm : ∀ x y : α, x + y = y + x

export AddCommMagma (add_comm)

instance lt_pnat : LT PNat :=
  ⟨fun x y => x.1 < y.1⟩

@[simp] theorem PNat.lt_def (x y : PNat) : x < y ↔ x.1 < y.1 := by rfl

theorem Nat.pos_add {x y : Nat} (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by
  omega

instance : Add PNat where
  add a b := ⟨a.val + b.val, Nat.pos_add a.property b.property⟩

@[simp] theorem PNat.add_def (x y : PNat) : x + y = ⟨x.val + y.val, Nat.pos_add x.property y.property⟩ := rfl

instance : AddCommMagma PNat where
  add a b := Add.add a b
  add_comm a b := by simp [Nat.add_comm]

theorem LT.lt.trans_eq [LT α] {x y : α} : x < y → y = z → x < z := by
  intro h₁ h₂; rwa [h₂] at h₁

theorem PNat.lt_add_left (m n : PNat) : n < m + n := by
  simp [m.property]

-- Here we use the `Add PNat` instance for the `+` notation.
-- set_option pp.all true in
-- #check PNat.lt_add_left

-- Here we use the `AddCommMagma.toAdd` instance.
-- set_option pp.all true in
-- #check add_comm

-- The instances are defeq at `instances` transparency, but not at `reducible`
-- transparency.

example (n m : PNat) : n < n + m := by
  saturate [LT.lt.trans_eq, PNat.lt_add_left, add_comm]
  assumption
