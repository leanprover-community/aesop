/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- Ported from mathlib3, file src/data/list/basic.lean,
-- commit a945b3769cb82bc238ee004b4327201a6864e7e0

import Aesop

set_option aesop.check.script true

-- We use this constant to 'prove' theorems which Aesop can't solve. We don't
-- use `sorry` because it generates lots of warnings.
axiom ADMIT : ∀ {α : Sort _}, α

@[aesop safe cases]
class IsEmpty (α : Sort _) where
  false : α → False

@[aesop safe forward]
def IsEmpty.false' (h : IsEmpty α) (a : α) : False :=
  h.false a

@[aesop safe constructors]
structure Unique (α : Sort _) extends Inhabited α where
  uniq : ∀ a : α, a = toInhabited.default

class IsLeftId (α : Type _) (op : α → α → α) (o : outParam α) : Prop where
  leftId : ∀ a, op o a = a

def Injective (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

@[aesop safe forward]
theorem injective_elim (h₁ : Injective f) (h₂ : f a = f b) : a = b :=
  h₁ _ _ h₂

@[aesop 99%]
theorem injective_intro (h : ∀ a b, f a = f b → a = b) : Injective f :=
  h

def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

@[aesop norm (forward (immediate := [h]))]
theorem surjective_elim (h : Surjective f) : ∀ b, ∃ a, f a = b :=
  h

@[aesop 99%]
theorem surjective_intro (h : ∀ b, ∃ a, f a = b) : Surjective f :=
  h

@[aesop norm unfold]
def Bijective (f : α → β) : Prop :=
  Injective f ∧ Surjective f

def Involutive (f : α → α) : Prop :=
  ∀ x, f (f x) = x

@[aesop norm forward]
theorem involutive_elim {f : α → α} (h : Involutive f) (a : α) : f (f a) = a :=
  h a

@[aesop 99%]
theorem involutive_intro (h : ∀ a, f (f a) = a) : Involutive f :=
  h

@[aesop 25%]
theorem Involutive.injective : Involutive f → Injective f :=
  λ h x y hxy => by rw [← h x, ← h y, hxy]

@[aesop 25%]
theorem Involutive.surjective : Involutive f → Surjective f :=
  λ h x => ⟨f x, h x⟩

theorem Involutive.bijective (h : Involutive f) : Bijective f :=
  ⟨h.injective, h.surjective⟩

namespace Option

@[aesop safe [constructors, cases]]
inductive Mem (a : α) : Option α → Prop
  | some : Mem a (some a)

instance : Membership α (Option α) :=
  ⟨Option.Mem⟩

@[simp]
theorem mem_spec {o : Option α} : a ∈ o ↔ o = some a := by
  aesop (add norm simp Membership.mem)

@[simp]
theorem mem_none : a ∈ none ↔ False := by
  aesop

@[simp]
theorem mem_some : a ∈ some b ↔ a = b := by
  aesop

@[simp]
def iget [Inhabited α] : Option α → α
  | none => default
  | some a => a

end Option

namespace List

-- The `ext` rule for lists says that `l₁ = l₂ ↔ (∀ a, a ∈ l₁ ↔ a ∈ l₂)`. This
-- is not particularly helpful for this file.
attribute [-aesop] Aesop.BuiltinRules.ext

attribute [simp] map List.bind

instance : Pure List where
  pure x := [x]

def init : List α → List α
  | [] => []
  | [_] => []
  | a :: as => a :: init as

@[simp]
def last : (l : List α) → l ≠ [] → α
  | [], h => nomatch h
  | [a], _ => a
  | _ :: a :: as, _ => last (a :: as) (by aesop)

-- The unnecessarily complicated case split in this definition is inherited from
-- Lean 3.
@[simp]
def ilast [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => ilast l

@[simp]
def head' : List α → Option α
  | [] => none
  | a :: _ => some a

@[simp]
def ihead [Inhabited α] : List α → α
  | [] => default
  | a :: _ => a

@[simp]
def nth_le : ∀ (l : List α) (n), n < l.length → α
  | [],       n,     h => absurd h n.not_lt_zero
  | (a :: _), 0,     _ => a
  | (_ :: l), (n+1), h => nth_le l n (by simp_all_arith)

@[simp]
def modify_head (f : α → α) : List α → List α
  | [] => []
  | (a :: as) => f a :: as

@[simp]
def Empty : List α → Prop
  | [] => True
  | _ :: _ => False

@[simp] theorem mem_eq_mem : Mem x xs ↔ x ∈ xs := Iff.rfl

theorem subset_trans {l₁ l₂ l₃ : List α} : l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃ := by
  intro h₁ h₂ a ha
  cases l₁ with
  | nil =>
    cases ha
  | cons x xs =>
    cases ha with
    | head =>
      apply h₂
      apply h₁
      constructor
    | tail _ hxs =>
      apply h₂
      apply h₁
      constructor
      assumption

-- END PRELUDE

instance unique_of_is_empty [IsEmpty α] : Unique (List α) := by
  aesop (add 1% cases List)

-- instance : is_left_id (list α) has_append.append [] :=
-- ⟨ nil_append ⟩

-- instance : is_right_id (list α) has_append.append [] :=
-- ⟨ append_nil ⟩

-- instance : is_associative (list α) has_append.append :=
-- ⟨ append_assoc ⟩

-- attribute [-simp] cons_ne_nil
theorem X.cons_ne_nil (a : α) (l : List α) : a::l ≠ [] := by
  aesop

-- attribute [-simp] cons_ne_self
theorem X.cons_ne_self (a : α) (l : List α) : a::l ≠ l := by
  aesop (add 1% cases Eq)

-- attribute [-simp] head_eq_of_cons_eq
theorem X.head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ := by
  aesop

-- attribute [-simp] tail_eq_of_cons_eq
theorem X.tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ := by
  aesop

@[simp] theorem cons_injective {a : α} : Injective (cons a) := by
  aesop

-- attribute [-simp] cons_inj
theorem X.cons_inj (a : α) {l l' : List α} : a::l = a::l' ↔ l = l' := by
  aesop

-- attribute [-simp] exists_cons_of_ne_nil
theorem X.exists_cons_of_ne_nil : l ≠ nil → ∃ b L, l = b :: L := by
  aesop (add 1% cases List)

-- theorem set_of_mem_cons (l : list α) (a : α) : {x | x ∈ a :: l} = insert a {x | x ∈ l} := rfl

/-! ### mem -/

attribute [aesop safe constructors] List.Mem
attribute [aesop safe (cases (patterns := [List.Mem _ [], List.Mem _ (_ :: _)]))] List.Mem

-- attribute [-simp] mem_singleton_self
@[simp]
theorem X.mem_singleton_self (a : α) : a ∈ [a] := by
  aesop

attribute [-simp] mem_singleton
-- attribute [-simp] eq_of_mem_singleton
theorem X.eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b := by
  aesop

@[simp]
theorem X.mem_singleton {a b : α} : a ∈ [b] ↔ a = b := by
  aesop

-- attribute [-simp] mem_of_mem_cons_of_mem
theorem X.mem_of_mem_cons_of_mem {a b : α} {l : List α} : a ∈ b::l → b ∈ l → a ∈ l := by
  aesop

set_option linter.unusedVariables false in
theorem _root_.decidable.list.eq_or_ne_mem_of_mem [deq : DecidableEq α]
  {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
  ADMIT
  -- cases deq a b <;> aesop

-- attribute [-simp] eq_or_ne_mem_of_mem
theorem X.eq_or_ne_mem_of_mem {a b : α} {l : List α} : a ∈ b :: l → a = b ∨ (a ≠ b ∧ a ∈ l) := by
  open Classical in
  aesop (add safe [decidable.list.eq_or_ne_mem_of_mem])

-- attribute [-simp] not_mem_append
theorem X.not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t := by
  induction s <;> aesop

-- attribute [-simp] ne_nil_of_mem
theorem X.ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  aesop

set_option linter.unusedVariables false in
theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t :=
  ADMIT -- Nontrivial existential.

-- attribute [-simp] mem_of_ne_of_mem
theorem X.mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l := by
  aesop

-- attribute [-simp] ne_of_not_mem_cons
theorem X.ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ≠ b := by
  aesop

-- attribute [-simp] not_mem_of_not_mem_cons
theorem X.not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ∉ l := by
  aesop

-- attribute [-simp] not_mem_cons_of_ne_of_not_mem
theorem X.not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l := by
  aesop

-- attribute [-simp] ne_and_not_mem_of_not_mem_cons
theorem X.ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y::l → a ≠ y ∧ a ∉ l := by
  aesop

-- attribute [-simp] mem_map
@[simp] theorem X.mem_map {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b := by
  induction l <;> aesop

-- attribute [-simp] mem_map_of_mem
@[aesop safe]
theorem X.mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l := by
  aesop

theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
  f a ∈ map f l ↔ a ∈ l := by
  aesop

@[simp] theorem _root_.function.involutive.exists_mem_and_apply_eq_iff {f : α → α}
  (hf : Involutive f) (x : α) (l : List α) :
  (∃ (y : α), y ∈ l ∧ f y = x) ↔ f x ∈ l := by
  set_option aesop.check.script false in -- TODO
  aesop

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
  a ∈ map f l ↔ f a ∈ l := by
  aesop

-- attribute [-simp] forall_mem_map_iff
theorem X.forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
  (∀ i, i ∈ l.map f → P i) ↔ ∀ j, j ∈ l → P (f j) := by
  aesop

attribute [-simp] map_eq_nil
@[simp] theorem X.map_eq_nil {f : α → β} {l : List α} : map f l = [] ↔ l = [] := by
  aesop (add 1% cases List)

-- attribute [-simp] mem_join
@[simp] theorem X.mem_join {a : α} : ∀ {L : List (List α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  intro L; induction L <;> aesop

-- attribute [-simp] exists_of_mem_join
theorem X.exists_of_mem_join {a : α} {L : List (List α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l := by
  aesop

-- attribute [-simp] mem_join_of_mem
theorem X.mem_join_of_mem {a : α} {L : List (List α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L := by
  aesop

-- attribute [-simp] mem_bind
@[simp] theorem X.mem_bind {b : β} {l : List α} {f : α → List β} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  induction l <;> aesop

-- attribute [-simp] exists_of_mem_bind
theorem X.exists_of_mem_bind {l : List α} :
    b ∈ l.bind f → ∃ a, a ∈ l ∧ b ∈ f a := by
  aesop

-- attribute [-simp] mem_bind_of_mem
theorem X.mem_bind_of_mem {l : List α} :
    (∃ a, a ∈ l ∧ b ∈ f a) → b ∈ l.bind f := by
  induction l <;> aesop

-- attribute [-simp] bind_map
theorem X.bind_map {g : α → List β} {f : β → γ} :
  ∀ l : List α, map f (l.bind g) = l.bind (λa => (g a).map f) := by
  intro l; induction l <;> aesop

theorem map_bind (g : β → List γ) (f : α → β) :
  ∀ l : List α, (map f l).bind g = l.bind (λ a => g (f a)) := by
  intro l; induction l <;> aesop

-- theorem range_map (f : α → β) : set.range (map f) = {l | ∀ x ∈ l, x ∈ set.range f} :=

-- theorem range_map_coe (s : set α) : set.range (map (coe : s → α)) = {l | ∀ x ∈ l, x ∈ s} :=

-- instance [h : can_lift α β] : can_lift (list α) (list β) :=

/-! ### length -/

-- attribute [-simp] length_eq_zero
theorem X.length_eq_zero {l : List α} : length l = 0 ↔ l = [] := by
  aesop (add 1% cases List)

attribute [-simp] length_singleton
@[simp] theorem X.length_singleton (a : α) : length [a] = 1 := rfl

-- attribute [-simp] length_pos_of_mem
theorem X.length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l := by
  aesop (add 1% cases List) (simp_options := { arith := true })

-- attribute [-simp] exists_mem_of_length_pos
theorem X.exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l := by
  aesop (add 1% cases List)

-- attribute [-simp] length_pos_iff_exists_mem
theorem X.length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l := by
  aesop (add unsafe [length_pos_of_mem, exists_mem_of_length_pos])

theorem ne_nil_of_length_pos {l : List α} : 0 < length l → l ≠ [] := by
  aesop (add 1% cases List)

theorem length_pos_of_ne_nil {l : List α} : l ≠ [] → 0 < length l := by
  aesop (add 1% cases List) (simp_options := { arith := true })

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] := by
  aesop (add unsafe [ne_nil_of_length_pos, length_pos_of_ne_nil])

-- attribute [-simp] exists_mem_of_ne_nil
theorem X.exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l := by
  aesop (add 1% cases List)

-- attribute [-simp] length_eq_one
theorem X.length_eq_one : length l = 1 ↔ ∃ a, l = [a] := by
  aesop (add 1% cases List)

theorem exists_of_length_succ {n} :
  ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t := by
  intro l; induction l <;> aesop (simp_options := { arith := true })

@[simp] theorem length_injective_iff : Injective (length : List α → Nat) ↔ Subsingleton α :=
  ADMIT -- Requires induction after case split.

@[simp] theorem length_injective [Subsingleton α] : Injective (length : List α → Nat) := by
  aesop

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] := by
  aesop (add 50% cases List)

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] := by
  aesop (add 50% cases List)

/-! ### set-theoretic notation of lists -/

attribute [-simp] empty_eq
theorem X.empty_eq : (∅ : List α) = [] := rfl

-- theorem singleton_eq (x : α) : ({x} : List α) = [x]

-- theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
--   has_insert.insert x l = x :: l

-- theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
--   has_insert.insert x l = l

-- theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y]

/-! ### bounded quantifiers over lists -/

-- The notation used in Lean 3 (`∀ x ∈ xs, P x` and `∃ x ∈ xs, P x`) does not
-- exist in Lean 4. We've expanded it manually.

-- attribute [-simp] forall_mem_nil
theorem X.forall_mem_nil (p : α → Prop) : ∀ x, x ∈ @nil α → p x := by
  aesop

-- attribute [-simp] forall_mem_cons
theorem X.forall_mem_cons : ∀ {p : α → Prop} {a : α} {l : List α},
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x := by
  aesop

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x, x ∈ a :: l → p x) :
  ∀ x, x ∈ l → p x := by
  aesop

-- attribute [-simp] forall_mem_singleton
theorem X.forall_mem_singleton {p : α → Prop} {a : α} : (∀ x, x ∈ [a] → p x) ↔ p a := by
  aesop

-- attribute [-simp] forall_mem_append
theorem X.forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ x, x ∈ l₁ ++ l₂ → p x) ↔ (∀ x, x ∈ l₁ → p x) ∧ (∀ x, x ∈ l₂ → p x) := by
  aesop

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x, x ∈ @nil α ∧ p x := by
  aesop

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) :
    ∃ x, x ∈ a :: l ∧ p x := by
  aesop

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} (h : ∃ x, x ∈ l ∧ p x) :
  ∃ x, x ∈ a :: l ∧ p x := by
  aesop

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∃ x, x ∈ a :: l ∧ p x) :
  p a ∨ ∃ x, x ∈ l ∧ p x := by
  aesop

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
  (∃ x, x ∈ a :: l ∧ p x) ↔ p a ∨ ∃ x, x ∈ l ∧ p x := by
  aesop

/-! ### list subset -/

-- attribute [-simp] subset_def
theorem X.subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ := by
  aesop

-- attribute [-simp] subset_append_of_subset_left
theorem X.subset_append_of_subset_left (l l₁ l₂ : List α) : l ⊆ l₁ → l ⊆ l₁++l₂ := by
  aesop (add 1% subset_trans)

-- attribute [-simp] subset_append_of_subset_right
theorem X.subset_append_of_subset_right (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ := by
  aesop (add 1% subset_trans)

attribute [-simp] cons_subset
@[simp] theorem X.cons_subset {a : α} {l m : List α} :
  a::l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  aesop (add norm simp [HasSubset.Subset, List.Subset])

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
    (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m := by
  aesop

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l := by
  aesop (add norm simp [HasSubset.Subset, List.Subset])

@[simp] theorem append_subset_iff {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  aesop (add norm simp [HasSubset.Subset, List.Subset])

@[aesop safe destruct]
theorem eq_nil_of_subset_nil {l : List α} : l ⊆ [] → l = [] := by
  aesop (add 1% cases List)

-- attribute [-simp] eq_nil_iff_forall_not_mem
theorem X.eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  aesop (add 1% cases List)

-- attribute [-simp] map_subset
theorem X.map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ := by
  aesop (add norm simp [HasSubset.Subset, List.Subset])

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  induction l₁ <;> induction l₂ <;> aesop

/-! ### append -/

theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ := rfl

attribute [-simp] singleton_append
@[simp] theorem X.singleton_append {x : α} {l : List α} : [x] ++ l = x :: l := rfl

-- attribute [-simp] append_ne_nil_of_ne_nil_left
theorem X.append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by
  induction s <;> aesop

-- attribute [-simp] append_ne_nil_of_ne_nil_right
theorem X.append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by
  induction s <;> aesop

attribute [-simp] append_eq_nil
@[simp] theorem X.append_eq_nil {p q : List α} : (p ++ q) = [] ↔ p = [] ∧ q = [] := by
  aesop (add 1% cases List)

@[simp] theorem nil_eq_append_iff {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] := by
  induction a <;> aesop

theorem append_eq_cons_iff {a b c : List α} {x : α} :
  a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
  aesop (add 1% cases List)

theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
  aesop (add norm simp [append_eq_cons_iff, eq_comm])

-- attribute [-simp] append_eq_append_iff
theorem X.append_eq_append_iff {a b c d : List α} :
    a ++ b = c ++ d ↔ (∃a', c = a ++ a' ∧ b = a' ++ d) ∨ (∃c', a = c ++ c' ∧ d = c' ++ b) :=
  ADMIT -- Nontrivial existential.

attribute [-simp] take_append_drop
@[simp] theorem X.take_append_drop : ∀ (n : Nat) (l : List α), take n l ++ drop n l = l
  | 0        , a         => by aesop
  | (.succ _), []        => by aesop
  | (.succ n), (_ :: xs) => by
    have ih := take_append_drop n xs
    aesop

-- attribute [-simp] append_inj
@[aesop safe forward]
theorem X.append_inj :
  ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | []     , []     , t₁, t₂, h, _  => by aesop
  | (a::s₁), []     , t₁, t₂, _, hl => by aesop
  | []     , (b::s₂), t₁, t₂, _, hl => by aesop
  | (a::s₁), (b::s₂), t₁, t₂, h, hl => by
    have ih := @append_inj _ s₁ s₂ t₁ t₂
    aesop

-- attribute [-simp] append_inj_right
theorem X.append_inj_right {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : t₁ = t₂ := by
  aesop

-- attribute [-simp] append_inj_left
theorem X.append_inj_left {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : s₁ = s₂ := by
  aesop

-- attribute [-simp] append_inj'
set_option linter.unusedVariables false in
@[aesop safe forward]
theorem X.append_inj' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
  s₁ = s₂ ∧ t₁ = t₂ := by
  induction s₁ generalizing s₂ <;> induction s₂ <;>
    aesop (simp_options := { arith := true })

-- attribute [-simp] append_inj_right'
theorem X.append_inj_right' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : t₁ = t₂ := by
  aesop

-- attribute [-simp] append_inj_left'
theorem X.append_inj_left' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : s₁ = s₂ := by
  aesop

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ := by
  aesop

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ := by
  aesop

theorem append_right_injective (s : List α) : Injective (λ t => s ++ t) := by
  aesop

-- attribute [-simp] append_right_inj
theorem X.append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ := by
  aesop

theorem append_left_injective (t : List α) : Injective (λ s => s ++ t) := by
  aesop

-- attribute [-simp] append_left_inj
theorem X.append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ := by
  aesop

-- attribute [-simp] map_eq_append_split
set_option linter.unusedVariables false in
theorem X.map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
    (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
  ADMIT -- Nontrivial existential.

/-! ### replicate/repeat -/

-- Note: `replicate` is called `repeat` in Lean 3 and has flipped arguments.

-- attribute [-simp] replicate_succ
@[simp] theorem X.replicate_succ (a : α) (n) : replicate (n + 1) a = a :: replicate n a := rfl

-- attribute [-simp] mem_replicate
@[simp] theorem X.mem_replicate {a b : α} {n} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a := by
  induction n <;> aesop

-- attribute [-simp] eq_of_mem_replicate
@[aesop safe destruct]
theorem X.eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := by
  aesop

-- attribute [-simp] eq_replicate_of_mem
theorem X.eq_replicate_of_mem {a : α} {l : List α} : (∀ b, b ∈ l → b = a) → l = replicate l.length a := by
  induction l <;> aesop (simp_options := { useHyps := false })

theorem eq_replicate' {a : α} {l : List α} : l = replicate l.length a ↔ ∀ b, b ∈ l → b = a := by
  induction l <;> aesop

-- attribute [-simp] eq_replicate
theorem X.eq_replicate {a : α} {n} {l : List α} : l = replicate n a ↔ length l = n ∧ ∀ b, b ∈ l → b = a := by
  set_option aesop.check.script false in -- TODO
  aesop (add norm simp eq_replicate')

theorem replicate_add (a : α) (m n) : replicate (m + n) a = replicate m a ++ replicate n a :=
  ADMIT -- Need to apply associativity of addition to let `replicate` reduce.

theorem replicate_subset_singleton (a : α) (n) : replicate n a ⊆ [a] := by
  set_option aesop.check.script false in -- TODO
  aesop (add norm simp [HasSubset.Subset, List.Subset])

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a :=
  ADMIT -- Nontrivial existential.

@[simp] theorem map_const (l : List α) (b : β) : map (λ _ => b) l = replicate l.length b := by
  induction l <;> aesop

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (λ _ => b₂) l) :
  b₁ = b₂ := by
  aesop

@[simp] theorem map_replicate (f : α → β) (a : α) (n) : map f (replicate n a) = replicate n (f a) := by
  induction n <;> aesop

@[simp] theorem tail_replicate (a : α) (n) : tail (replicate n a) = replicate n.pred a := by
  aesop (add 1% cases Nat)

@[simp] theorem join_replicate_nil (n : Nat) : join (replicate n []) = @nil α := by
  induction n <;> aesop

theorem replicate_left_injective {n : Nat} (hn : n ≠ 0) :
    Injective (λ a : α => replicate n a) := by
  induction n <;> aesop

@[simp] theorem replicate_left_inj' {a b : α} :
  ∀ {n}, replicate n a = replicate n b ↔ n = 0 ∨ a = b := by
  intro n; induction n <;> aesop

theorem replicate_right_injective (a : α) : Injective (λ n => replicate n a) := by
  unfold Injective; intro x y
  induction x generalizing y <;> induction y <;>
    aesop (simp_options := { useHyps := false })

@[simp] theorem replicate_right_inj {a : α} {n m : Nat} :
    replicate n a = replicate m a ↔ n = m := by
  induction n generalizing m <;> aesop (add 1% cases Nat)

/-! ### pure -/

@[simp]
theorem mem_pure {α} (x y : α) :
    x ∈ (pure y : List α) ↔ x = y := by
  set_option aesop.check.script false in -- TODO
  aesop (add norm simp pure)

/-! ### bind -/

instance : Bind List where
  bind l f := List.bind l f

@[simp] theorem bind_eq_bind {α β} (f : α → List β) (l : List α) :
    l >>= f = l.bind f := rfl

theorem bind_append (f : α → List β) (l₁ l₂ : List α) :
  (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f := by
  induction l₁ <;> aesop

@[simp] theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x := by
  aesop

@[simp] theorem bind_singleton' (l : List α) : l.bind (λ x => [x]) = l := by
  induction l <;> aesop

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind (λ x => [f x]) := by
  induction l <;> aesop

theorem bind_assoc {α β γ : Type u} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind (λ x => (f x).bind g) :=
  ADMIT
  -- have aux {δ : Type u} (xs ys : List (List δ)) : join (xs ++ ys) = join xs ++ join ys := by
  --   induction xs <;> aesop
  -- induction l <;> aesop (add norm [simp [bind_append], unfold [bind]])

/-! ### concat -/

@[simp] theorem concat_nil (a : α) : concat [] a = [a] := rfl

@[simp] theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b := rfl

attribute [-simp] concat_eq_append
@[simp] theorem X.concat_eq_append (a : α) (l : List α) : concat l a = l ++ [a] := by
  induction l <;> aesop

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := by
  aesop

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b := by
  aesop

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by
  aesop

attribute [simp] append_assoc

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by
  aesop

attribute [-simp] length_concat
theorem X.length_concat (a : α) (l : List α) : length (concat l a) = .succ (length l) := by
  aesop

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by
  aesop

/-! ### reverse -/

attribute [-simp] reverse_nil
@[simp] theorem X.reverse_nil : reverse (@nil α) = [] := rfl

attribute [-simp] reverse_cons
@[simp] theorem X.reverse_cons (a : α) (l : List α) : reverse (a::l) = reverse l ++ [a] :=
  ADMIT
  -- have aux : ∀ l₁ l₂, reverseAux l₁ l₂ ++ [a] = reverseAux l₁ (l₂ ++ [a]) := by
  --   intro l₁; induction l₁ <;> aesop (add norm unfold reverseAux)
  -- aesop (add norm unfold reverse)

-- Note: reverse_core is called reverseAux in Lean 4.
-- attribute [-simp] reverseAux_eq
@[simp]
theorem reverse_core_eq (l₁ l₂ : List α) : reverseAux l₁ l₂ = reverse l₁ ++ l₂ := by
  induction l₁ generalizing l₂ <;> aesop

theorem reverse_cons' (a : α) (l : List α) : reverse (a::l) = concat (reverse l) a := by
  aesop

@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] := rfl

attribute [-simp] reverse_append
@[simp] theorem X.reverse_append (s t : List α) : reverse (s ++ t) = (reverse t) ++ (reverse s) := by
  induction s <;> aesop

-- attribute [-simp] reverse_concat
theorem X.reverse_concat (l : List α) (a : α) : reverse (concat l a) = a :: reverse l := by
  aesop

attribute [-simp] reverse_reverse
@[simp] theorem X.reverse_reverse (l : List α) : reverse (reverse l) = l := by
  induction l <;> aesop

@[simp] theorem reverse_involutive : Involutive (@reverse α) := by
  aesop

@[simp] theorem reverse_injective {α : Type u} : Injective (@reverse α) := by
  aesop

@[simp] theorem reverse_surjective {α : Type u} : Surjective (@reverse α) := by
  aesop

@[simp] theorem reverse_bijective : Bijective (@reverse α) := by
  aesop

@[simp] theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ := by
  aesop (add safe forward reverse_injective)

theorem reverse_eq_iff {l l' : List α} :
  l.reverse = l' ↔ l = l'.reverse := by
  aesop

@[simp] theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] := by
  aesop (add norm simp reverse_eq_iff)

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  induction l <;> aesop

attribute [-simp] length_reverse
@[simp] theorem X.length_reverse (l : List α) : length (reverse l) = length l := by
  induction l <;> aesop

theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) := by
  induction l <;> aesop

-- attribute [-simp] map_reverseAux
theorem map_reverse_core (f : α → β) (l₁ l₂ : List α) :
  map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  aesop (add norm simp reverse_map)

attribute [-simp] mem_reverse
@[simp] theorem X.mem_reverse {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l := by
  induction l <;> aesop

@[simp] theorem reverse_replicate (a : α) (n) : reverse (replicate n a) = replicate n a :=
  ADMIT -- Several missing lemmas.

/-! ### empty -/

theorem empty_iff_eq_nil {l : List α} : Empty l ↔ l = [] := by
  aesop

/-! ### init -/

@[simp] theorem length_init : ∀ (l : List α), length (init l) = length l - 1
  | [] => by aesop
  | [_] => by aesop
  | (_ :: y :: zs) => by
    have ih := length_init (y :: zs)
    aesop (add norm simp [init, Nat.add_sub_cancel])

/-! ### last -/

@[simp] theorem last_cons {a : α} {l : List α} :
  ∀ (h : l ≠ nil), last (a :: l) (cons_ne_nil a l) = last l h := by
  aesop (add 1% cases List)

@[simp] theorem last_append_singleton {a : α} (l : List α) :
  last (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  induction l <;> aesop

theorem last_append (l₁ l₂ : List α) (h : l₂ ≠ []) :
  last (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = last l₂ h := by
  induction l₁ <;> aesop

theorem last_concat {a : α} (l : List α) : last (concat l a) (concat_ne_nil a l) = a := by
  aesop

@[simp] theorem last_singleton (a : α) : last [a] (cons_ne_nil a []) = a := rfl

@[simp] theorem last_cons_cons (a₁ a₂ : α) (l : List α) :
  last (a₁::a₂::l) (cons_ne_nil _ _) = last (a₂::l) (cons_ne_nil a₂ l) := rfl

theorem init_append_last : ∀ {l : List α} (h : l ≠ []), init l ++ [last l h] = l
  | [] => by aesop
  | [_] => by aesop
  | x :: y :: zs => by
    have ih := init_append_last (l := y :: zs)
    aesop (add norm simp [init, last])

theorem last_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ := by
  aesop

theorem last_mem : ∀ {l : List α} (h : l ≠ []), last l h ∈ l := by
  intro l; induction l <;> aesop (add norm simp last, 1% cases List)

theorem last_replicate_succ (a m : Nat) :
  (replicate m.succ a).last
    (ne_nil_of_length_eq_succ
      (show (replicate m.succ a).length = m.succ by rw [length_replicate])) =
  a := by
  induction m <;> aesop

/-! ### last' -/

@[simp] theorem last'_is_none :
  ∀ {l : List α}, (last' l).isNone ↔ l = []
  | [] => by aesop
  | [a] => by aesop
  | a :: a' :: as => by
    have ih := last'_is_none (l := a' :: as)
    aesop

@[simp] theorem last'_is_some : ∀ {l : List α}, l.last'.isSome ↔ l ≠ []
  | [] => by aesop
  | [a] => by aesop
  | a :: a' :: as => by
    have ih := last'_is_some (l := a' :: as)
    aesop

theorem mem_last'_eq_last : ∀ {l : List α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
  | [], _, h => by aesop
  | [_], _, h => by aesop
  | a :: a' :: as, x, h => by
    have ih := mem_last'_eq_last (l := a' :: as) (x := x)
    aesop (add norm simp last')

theorem last'_eq_last_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.last' = some (l.last h)
  | [], h => by aesop
  | [a], _ => by aesop
  | _ :: b :: l, _ => by
    have ih := last'_eq_last_of_ne_nil (l := b :: l)
    aesop

theorem mem_last'_cons {x y : α} : ∀ {l : List α} (_ : x ∈ l.last'), x ∈ (y :: l).last' := by
  intro l; induction l <;> aesop

theorem mem_of_mem_last' {l : List α} {a : α} (ha : a ∈ l.last') : a ∈ l := by
  match l with
  | [] => aesop
  | [_] => aesop
  | x :: y :: zs =>
    have ih := mem_of_mem_last' (l := y :: zs) (a := a)
    aesop

theorem init_append_last' : ∀ {l : List α} {a}, a ∈ l.last' → init l ++ [a] = l
  | [], _ => by aesop
  | [_], _ => by aesop
  | x :: y :: zs, a => by
    have ih := init_append_last' (l := y :: zs) (a := a)
    aesop (add norm simp init)

theorem ilast_eq_last' [Inhabited α] : ∀ l : List α, l.ilast = l.last'.iget
  | [] => by aesop
  | [a] => by aesop
  | [_, _] => by aesop
  | [_, _, _] => by aesop
  | (_ :: _ :: c :: l) => by
    have ih := ilast_eq_last' (c :: l)
    aesop

@[simp] theorem last'_append_cons : ∀ (l₁ : List α) (a : α) (l₂ : List α),
  last' (l₁ ++ a :: l₂) = last' (a :: l₂)
  | [], a, l₂ => by aesop
  | [_], a, l₂ => by aesop
  | _ :: c :: l₁, a, l₂ =>
    have ih := last'_append_cons (c :: l₁) a
    by aesop

@[simp] theorem last'_cons_cons (x y : α) (l : List α) :
  last' (x :: y :: l) = last' (y :: l) := rfl

theorem last'_append_of_ne_nil (l₁ : List α) : ∀ {l₂ : List α} (_ : l₂ ≠ []),
  last' (l₁ ++ l₂) = last' l₂
  | [], hl₂ => by aesop
  | b :: l₂, _ => by aesop

theorem last'_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.last') :
  x ∈ (l₁ ++ l₂).last' := by
  aesop (add 1% cases List)

/-! ### head(') and tail -/

-- Note: Lean 3 head is Lean 4 ihead.

-- attribute [-simp] ihead_eq_head'
theorem head_eq_head' [Inhabited α] (l : List α) : ihead l = (head' l).iget := by
  aesop (add 1% cases List)

theorem mem_of_mem_head' {x : α} : ∀ {l : List α}, x ∈ l.head' → x ∈ l := by
  intro l; induction l <;> aesop

-- attribute [-simp] head'_cons
@[simp] theorem X.head'_cons [Inhabited α] (a : α) (l : List α) : head' (a::l) = a := rfl

attribute [-simp] tail_nil
@[simp] theorem X.tail_nil : tail (@nil α) = [] := rfl

attribute [-simp] tail_cons
@[simp] theorem X.tail_cons (a : α) (l : List α) : tail (a::l) = l := rfl

-- attribute [-simp] ihead_append
@[simp] theorem head_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
  ihead (s ++ t) = ihead s := by
  aesop (add 1% cases List)

theorem head'_append {s t : List α} {x : α} (h : x ∈ s.head') :
  x ∈ (s ++ t).head' := by
  aesop (add 1% cases List)

theorem head'_append_of_ne_nil : ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []),
  head' (l₁ ++ l₂) = head' l₁ := by
  aesop (add 1% cases List)

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
  tail (l ++ [a]) = tail l ++ [a] := by
  induction l <;> aesop

theorem cons_head'_tail : ∀ {l : List α} {a : α} (_ : a ∈ head' l), a :: tail l = l := by
  aesop

-- attribute [-simp] ihead_mem_head'
theorem head_mem_head' [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), ihead l ∈ head' l := by
  aesop

-- attribute [-simp] cons_ihead_tail
theorem cons_head_tail [Inhabited α] {l : List α} (h : l ≠ []) : (ihead l)::(tail l) = l := by
  aesop

end List
