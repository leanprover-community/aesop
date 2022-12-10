/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std

-- Ported from mathlib3, file src/data/list/basic.lean,
-- commit a945b3769cb82bc238ee004b4327201a6864e7e0

-- We use this constant to 'prove' theorems which Aesop can't solve. We don't
-- use `sorry` because it generates lots of warnings.
axiom ADMIT : ∀ {α : Sort _}, α

class IsEmpty (α : Sort _) where
  false : α → False

def IsEmpty.false' (h : IsEmpty α) (a : α) : False :=
  h.false a

structure Unique (α : Sort _) extends Inhabited α where
  uniq : ∀ a : α, a = toInhabited.default

class IsLeftId (α : Type _) (op : α → α → α) (o : outParam α) : Prop where
  leftId : ∀ a, op o a = a

def Injective (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y

theorem injective_elim (h₁ : Injective f) (h₂ : f a = f b) : a = b :=
  h₁ _ _ h₂

theorem injective_intro (h : ∀ a b, f a = f b → a = b) : Injective f :=
  h

theorem Injective.eq_iff : Injective f → (f x = f y ↔ x = y) :=
  λ (h : Injective f) => ⟨λ h₂ => h _ _ h₂, λ eq => by rw [eq]⟩

def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

theorem surjective_elim (h : Surjective f) : ∀ b, ∃ a, f a = b :=
  h

theorem surjective_intro (h : ∀ b, ∃ a, f a = b) : Surjective f :=
  h

def Bijective (f : α → β) : Prop :=
  Injective f ∧ Surjective f

def Involutive (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involutive_elim {f : α → α} (h : Involutive f) (a : α) : f (f a) = a :=
  h a

theorem involutive_intro (h : ∀ a, f (f a) = a) : Involutive f :=
  h

theorem Involutive.injective : Involutive f → Injective f :=
  λ h x y hxy => by rw [← h x, ← h y, hxy]

theorem Involutive.surjective : Involutive f → Surjective f :=
  λ h x => ⟨f x, h x⟩

theorem Involutive.bijective (h : Involutive f) : Bijective f :=
  ⟨h.injective, h.surjective⟩

theorem Involutive.eq_iff : Involutive f → (f x = y ↔ x = f y) :=
  λ h => by constructor <;> intro h' <;> subst h' <;> rw [h]

namespace Option

inductive Mem (a : α) : Option α → Prop
  | some : Mem a (some a)

instance : Membership α (Option α) :=
  ⟨Option.Mem⟩

@[simp]
theorem mem_spec {o : Option α} : a ∈ o ↔ o = some a :=
  ⟨λ | .some => rfl, λ h => by rw [h]; exact .some⟩

@[simp]
theorem mem_none : a ∈ none ↔ False :=
  ⟨fun., λ h => h.elim⟩

@[simp]
theorem mem_some : a ∈ some b ↔ a = b :=
  ⟨λ | .some => rfl, λ h => by rw [h]; exact .some⟩

@[simp]
def iget [Inhabited α] : Option α → α
  | none => default
  | some a => a

end Option

namespace List

attribute [simp] map List.bind

instance : Pure List where
  pure x := [x]

def init : List α → List α
  | [] => []
  | [_] => []
  | a :: as => a :: init as

@[simp]
def last : (l : List α) → l ≠ [] → α
  | [a], _ => a
  | _ :: a :: as, _ => last (a :: as) (by simp)

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


instance unique_of_is_empty [inst : IsEmpty α] : Unique (List α) := by
  cases inst with | _ contra =>
  apply Unique.mk
  . intro xs
    cases xs with
    | nil => rfl
    | cons x _ => exact contra x |>.elim

-- SKIP NA
-- instance : is_left_id (list α) has_append.append [] :=
-- ⟨ nil_append ⟩

-- SKIP NA
-- instance : is_right_id (list α) has_append.append [] :=
-- ⟨ append_nil ⟩

-- SKIP NA
-- instance : is_associative (list α) has_append.append :=
-- ⟨ append_assoc ⟩

-- attribute [-simp] cons_ne_nil
theorem X.cons_ne_nil (a : α) (l : List α) : a::l ≠ [] :=
  fun.

-- attribute [-simp] cons_ne_self
theorem X.cons_ne_self (a : α) (l : List α) : a::l ≠ l :=
  fun.

-- attribute [-simp] head_eq_of_cons_eq
theorem X.head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
  λ Peq => List.noConfusion Peq (λ Pheq _ => Pheq)

-- attribute [-simp] tail_eq_of_cons_eq
theorem X.tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
  λ Peq => List.noConfusion Peq (λ _ Pteq => Pteq)

@[simp] theorem cons_injective {a : α} : Injective (cons a) :=
  λ _ _ Pe => tail_eq_of_cons_eq Pe

-- attribute [-simp] cons_inj
theorem X.cons_inj (a : α) {l l' : List α} : a::l = a::l' ↔ l = l' :=
  ⟨λ h => cons_injective _ _ h, λ h => by rw [h]⟩

-- attribute [-simp] exists_cons_of_ne_nil
theorem X.exists_cons_of_ne_nil : l ≠ nil → ∃ b L, l = b :: L :=
  λ _ => match l with | nil => by contradiction | cons a as => ⟨a, as, rfl⟩

-- SKIP NA
-- theorem set_of_mem_cons (l : list α) (a : α) : {x | x ∈ a :: l} = insert a {x | x ∈ l} := rfl

/-! ### mem -/

-- attribute [-simp] mem_singleton_self
@[simp]
theorem X.mem_singleton_self (a : α) : a ∈ [a] :=
  mem_cons_self _ _

attribute [-simp] mem_singleton
-- attribute [-simp] eq_of_mem_singleton
theorem X.eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
  λ _ => by simp_all only [mem_cons, not_mem_nil, or_false]

@[simp]
theorem X.mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨X.eq_of_mem_singleton, λ h => by subst h; constructor⟩

-- attribute [-simp] mem_of_mem_cons_of_mem
theorem X.mem_of_mem_cons_of_mem {a b : α} {l : List α} : a ∈ b::l → b ∈ l → a ∈ l := λ ha hb =>
  match mem_cons.mp ha with
  | .inl (.refl _) => hb
  | .inr h => h

set_option linter.unusedVariables false in
theorem _root_.decidable.list.eq_or_ne_mem_of_mem [deq : DecidableEq α]
  {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
  ADMIT

-- attribute [-simp] eq_or_ne_mem_of_mem
theorem X.eq_or_ne_mem_of_mem {a b : α} {l : List α} : a ∈ b :: l → a = b ∨ (a ≠ b ∧ a ∈ l) :=
  ADMIT

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1 λ contra => by cases contra <;> contradiction

-- attribute [-simp] ne_nil_of_mem
theorem X.ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  intro e; rw [e] at h; cases h

set_option linter.unusedVariables false in
theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t :=
  ADMIT

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  match mem_cons.mp h₂ with | .inl e => absurd e h₁ | .inr r => r

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ≠ b :=
  λ nin aeqb => absurd (Or.inl aeqb) λ contra => nin (mem_cons.mpr contra)

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ∉ l :=
  λ nin aebq => absurd (Or.inl aebq) λ contra => nin (mem_cons.mpr (Or.comm.mp contra))

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l :=
  λ p1 p2 contra => absurd (mem_cons.mp contra) (by simp [p1, p2])

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
  λ p => ⟨ne_of_not_mem_cons p, not_mem_of_not_mem_cons p⟩

-- attribute [-simp] mem_map
@[simp] theorem X.mem_map {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all only [map, not_mem_nil, false_and, exists_false, iff_self]
  | cons =>
    simp_all only [map, mem_cons, exists_eq_or_imp]
    apply Iff.intro
    case mp =>
      intro h
      cases h with
      | inl h => exact .inl h.symm
      | inr h => exact .inr h
    case mpr =>
      intro h
      cases h with
      | inl h => exact .inl h.symm
      | inr h => exact .inr h

-- attribute [-simp] mem_map_of_mem
theorem X.mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l :=
  mem_map.2 ⟨a, h, rfl⟩

theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
  f a ∈ map f l ↔ a ∈ l :=
  ⟨λ m => let ⟨_, m', e⟩ := exists_of_mem_map m; H _ _ e ▸ m', mem_map_of_mem _⟩

@[simp] theorem _root_.function.involutive.exists_mem_and_apply_eq_iff {f : α → α}
  (hf : Involutive f) (x : α) (l : List α) :
  (∃ (y : α), y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by intro ⟨y, h₁, h₂⟩; rw [← h₂, hf]; exact h₁, λ h => ⟨f x, h, hf _⟩⟩

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
  a ∈ map f l ↔ f a ∈ l := by
  simp only [hf, X.mem_map, function.involutive.exists_mem_and_apply_eq_iff, iff_self]

-- attribute [-simp] forall_mem_map_iff
theorem X.forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
  (∀ i, i ∈ l.map f → P i) ↔ ∀ j, j ∈ l → P (f j) := by
  simp only [mem_map, exists_imp, and_imp]
  apply Iff.intro
  case mp =>
    intro h₁ x h₂
    exact h₁ _ _ h₂ rfl
  case mpr =>
    intro h₁ b a h₂ h₃
    subst h₃
    exact h₁ _ h₂

attribute [-simp] map_eq_nil
@[simp] theorem X.map_eq_nil {f : α → β} {l : List α} : map f l = [] ↔ l = [] :=
  ⟨by cases l <;> simp only [map, imp_self], λ h => h.symm ▸ rfl⟩

-- attribute [-simp] mem_join
@[simp] theorem X.mem_join {a : α} : ∀ {L : List (List α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  intro L
  induction L with
  | nil => simp_all only [join, not_mem_nil, false_and, exists_false, iff_self]
  | cons => simp_all only [join, mem_append, mem_cons, exists_eq_or_imp, iff_self]

-- attribute [-simp] exists_of_mem_join
theorem X.exists_of_mem_join {a : α} {L : List (List α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
  mem_join.1

-- attribute [-simp] mem_join_of_mem
theorem X.mem_join_of_mem {a : α} {L : List (List α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
  mem_join.2 ⟨l, lL, al⟩

-- attribute [-simp] mem_bind
@[simp] theorem X.mem_bind {b : β} {l : List α} {f : α → List β} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a :=
  Iff.trans mem_join
  ⟨λ ⟨_, h1, h2⟩ => let ⟨a, al, fa⟩ := exists_of_mem_map h1; ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩ => ⟨f a, mem_map_of_mem _ al, bfa⟩⟩

-- attribute [-simp] exists_of_mem_bind
theorem X.exists_of_mem_bind {l : List α} :
    b ∈ l.bind f → ∃ a, a ∈ l ∧ b ∈ f a :=
  mem_bind.1

-- attribute [-simp] mem_bind_of_mem
theorem X.mem_bind_of_mem {l : List α} :
    (∃ a, a ∈ l ∧ b ∈ f a) → b ∈ l.bind f :=
  mem_bind.2

-- attribute [-simp] bind_map
theorem X.bind_map {g : α → List β} {f : β → γ} :
  ∀(l : List α), map f (l.bind g) = l.bind (λa => (g a).map f) := by
  intro l; induction l with | nil => rfl | cons => simp_all only [List.bind, join, map_append]

theorem map_bind (g : β → List γ) (f : α → β) :
  ∀ l : List α, (map f l).bind g = l.bind (λ a => g (f a)) := by
  intro l; induction l with | nil => rfl | cons => simp_all only [List.bind, join, map_append]

-- SKIP NA
-- theorem range_map (f : α → β) : set.range (map f) = {l | ∀ x ∈ l, x ∈ set.range f} :=

-- SKIP NA
-- theorem range_map_coe (s : set α) : set.range (map (coe : s → α)) = {l | ∀ x ∈ l, x ∈ s} :=

-- SKIP NA
-- instance [h : can_lift α β] : can_lift (list α) (list β) :=

/-! ### length -/

-- attribute [-simp] length_eq_zero
theorem X.length_eq_zero {l : List α} : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, λ h => h.symm ▸ rfl⟩

-- SKIP TRIV
attribute [-simp] length_singleton
@[simp] theorem X.length_singleton (a : α) : length [a] = 1 := rfl

-- attribute [-simp] length_pos_of_mem
theorem X.length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | (_ :: _), _ => Nat.zero_lt_succ _

-- attribute [-simp] exists_mem_of_length_pos
theorem X.exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | (b :: _), _ => ⟨b, mem_cons_self _ _⟩

-- attribute [-simp] length_pos_iff_exists_mem
theorem X.length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, λ ⟨_, h⟩ => length_pos_of_mem h⟩

theorem ne_nil_of_length_pos {l : List α} : 0 < length l → l ≠ [] :=
  λ h1 h2 => Nat.lt_irrefl 0 ((length_eq_zero.2 h2).subst h1)

theorem length_pos_of_ne_nil {l : List α} : l ≠ [] → 0 < length l :=
  λ h => Nat.pos_iff_ne_zero.2 $ λ h0 => h $ length_eq_zero.1 h0

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

-- attribute [-simp] exists_mem_of_ne_nil
theorem X.exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos_of_ne_nil h)

-- attribute [-simp] length_eq_one
theorem X.length_eq_one : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨λ _ => match l with | [a] => ⟨a, rfl⟩, λ ⟨_, e⟩ => e.symm ▸ rfl⟩

theorem exists_of_length_succ {n} :
  ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm $ n.succ_ne_zero
  | (h :: t), _ => ⟨h, t, rfl⟩

@[simp] theorem length_injective_iff : Injective (length : List α → Nat) ↔ Subsingleton α :=
  ADMIT

@[simp] theorem length_injective [Subsingleton α] : Injective (length : List α → Nat) :=
  length_injective_iff.mpr inferInstance

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨λ _ => match l with | [a, b] => ⟨a, b, rfl⟩, λ ⟨_, _, e⟩ => e.symm ▸ rfl⟩

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨λ _ => match l with | [a, b, c] => ⟨a, b, c, rfl⟩, λ ⟨_, _, _, e⟩ => e.symm ▸ rfl⟩

/-! ### set-theoretic notation of lists -/

-- SKIP TRIV
attribute [-simp] empty_eq
theorem X.empty_eq : (∅ : List α) = [] := rfl

-- SKIP NA
-- theorem singleton_eq (x : α) : ({x} : List α) = [x]

-- SKIP NA
-- theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
--   has_insert.insert x l = x :: l

-- SKIP NA
-- theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) :
--   has_insert.insert x l = l

-- SKIP NA
-- theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y]

/-! ### bounded quantifiers over lists -/

-- Note: the notation used in Lean 3 (`∀ x ∈ xs, P x` and `∃ x ∈ xs, P x`) does
-- not exist in Lean 4. I've expanded it manually.

-- attribute [-simp] forall_mem_nil
theorem X.forall_mem_nil (p : α → Prop) : ∀ x, x ∈ @nil α → p x := by
  intros; contradiction

-- attribute [-simp] forall_mem_cons
theorem X.forall_mem_cons : ∀ {p : α → Prop} {a : α} {l : List α},
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x := by
  intros; simp only [mem_cons, forall_eq_or_imp, iff_self]

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x, x ∈ a :: l → p x) :
  ∀ x, x ∈ l → p x :=
  (forall_mem_cons.1 h).2

-- attribute [-simp] forall_mem_singleton
theorem X.forall_mem_singleton {p : α → Prop} {a : α} : (∀ x, x ∈ [a] → p x) ↔ p a := by
  simp only [mem_cons, not_mem_nil, or_false, forall_eq, iff_self]

-- attribute [-simp] forall_mem_append
theorem X.forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ x, x ∈ l₁ ++ l₂ → p x) ↔ (∀ x, x ∈ l₁ → p x) ∧ (∀ x, x ∈ l₂ → p x) := by
  simp only [mem_append]
  apply Iff.intro
  case mp => simp_all only [true_or, implies_true, or_true, and_self]
  case mpr =>
  · intro ⟨h₁, h₂⟩ a h₃
    cases h₃ <;> simp_all only

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x, x ∈ @nil α ∧ p x :=
  fun.

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) :
    ∃ x, x ∈ a :: l ∧ p x :=
  ⟨a, ⟨mem_cons_self a l, h⟩⟩

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} (h : ∃ x, x ∈ l ∧ p x) :
  ∃ x, x ∈ a :: l ∧ p x :=
  h.elim λ x ⟨xl, px⟩ => ⟨x, ⟨.tail _ xl, px⟩⟩

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∃ x, x ∈ a :: l ∧ p x) :
  p a ∨ ∃ x, x ∈ l ∧ p x := by
  simp_all only [mem_cons, exists_eq_or_imp]

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
  (∃ x, x ∈ a :: l ∧ p x) ↔ p a ∨ ∃ x, x ∈ l ∧ p x :=
  ⟨or_exists_of_exists_mem_cons, λ h => h.elim (exists_mem_cons_of l) exists_mem_cons_of_exists⟩

/-! ### list subset -/

-- attribute [-simp] subset_def
theorem X.subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ :=
  Iff.rfl

-- attribute [-simp] subset_append_of_subset_left
theorem X.subset_append_of_subset_left (l l₁ l₂ : List α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
  λ s => Subset.trans s $ subset_append_left _ _

-- attribute [-simp] subset_append_of_subset_right
theorem X.subset_append_of_subset_right (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
  λ s => Subset.trans s $ subset_append_right _ _

attribute [-simp] cons_subset
@[simp] theorem X.cons_subset {a : α} {l m : List α} :
  a::l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  simp only [HasSubset.Subset, List.Subset, mem_cons, forall_eq_or_imp, iff_self]

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
    (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
  cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
  λ _ h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

@[simp] theorem append_subset_iff {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  apply Iff.intro <;> intro h
  case mp => simp_all only [append_subset, and_self]
  case mpr => exact append_subset_of_subset_of_subset h.left h.right

theorem eq_nil_of_subset_nil (l : List α) : l ⊆ [] → l = [] := λ h =>
  match l with
  | nil => rfl
  | (_ :: _) => False.elim $ not_mem_nil _ $ (h (mem_cons_self _ _))

-- attribute [-simp] eq_nil_iff_forall_not_mem
theorem X.eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  apply Iff.intro <;> intro h
  · simp only [h, not_mem_nil, not_false_iff, implies_true]
  · cases l <;> simp_all

-- attribute [-simp] map_subset
theorem X.map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
  λ x => by simp only [mem_map, exists_imp, and_imp]; exact λ a h e => ⟨a, H h, e⟩

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine ⟨?_, map_subset f⟩; intros h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  cases h _ _ hxx'; exact hx'

/-! ### append -/

-- SKIP TRIV
theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ := rfl

-- SKIP TRIV
attribute [-simp] singleton_append
@[simp] theorem X.singleton_append {x : α} {l : List α} : [x] ++ l = x :: l := rfl

-- attribute [-simp] append_ne_nil_of_ne_nil_left
theorem X.append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by
  induction s <;> intros <;> intro <;> contradiction

-- attribute [-simp] append_ne_nil_of_ne_nil_right
theorem X.append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by
  induction s <;> intros <;> intro <;> contradiction

attribute [-simp] append_eq_nil
@[simp] theorem X.append_eq_nil {p q : List α} : (p ++ q) = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp only [nil_append, true_and, cons_append, false_and, iff_self]

@[simp] theorem nil_eq_append_iff {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]

theorem append_eq_cons_iff {a b c : List α} {x : α} :
  a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
  cases a <;>
    simp only [nil_append, true_and, @eq_comm _ c, false_and, exists_false, or_false,
               iff_self, and_assoc, cons_append, cons.injEq, exists_and_left, exists_eq_left', false_or]

theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) := by
  rw [eq_comm, append_eq_cons_iff]

-- attribute [-simp] append_eq_append_iff
theorem X.append_eq_append_iff {a b c d : List α} :
    a ++ b = c ++ d ↔ (∃a', c = a ++ a' ∧ b = a' ++ d) ∨ (∃c', a = c ++ c' ∧ d = c' ++ b) :=
  ADMIT

attribute [-simp] take_append_drop
@[simp] theorem X.take_append_drop : ∀ (n : Nat) (l : List α), take n l ++ drop n l = l
  | 0        , _         => rfl
  | (.succ _), []        => rfl
  | (.succ n), (x :: xs) => congrArg (cons x) $ take_append_drop n xs

-- attribute [-simp] append_inj
theorem X.append_inj :
  ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | []     , []     , t₁, t₂, h, _ => ⟨rfl, h⟩
  | (a::s₁), []     , t₁, t₂, _, hl => List.noConfusion $ eq_nil_of_length_eq_zero hl
  | []     , (b::s₂), t₁, t₂, _, hl => List.noConfusion $ eq_nil_of_length_eq_zero hl.symm
  | (a::s₁), (b::s₂), t₁, t₂, h, hl => List.noConfusion h $ λ ab hap =>
    let ⟨e1, e2⟩ := @append_inj _ s₁ s₂ t₁ t₂ hap (Nat.succ.inj hl)
    by rw [ab, e1, e2]; exact ⟨rfl, rfl⟩

-- attribute [-simp] append_inj_right
theorem X.append_inj_right {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

-- attribute [-simp] append_inj_left
theorem X.append_inj_left {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

-- attribute [-simp] append_inj'
set_option linter.unusedVariables false in
theorem X.append_inj' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
  s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h $ @Nat.add_right_cancel _ (length t₁) _ $
    let hap := congrArg length h; by simp only [length_append] at hap; rwa [← hl] at hap

-- attribute [-simp] append_inj_right'
theorem X.append_inj_right' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

-- attribute [-simp] append_inj_left'
theorem X.append_inj_left' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  append_inj_right h rfl

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  append_inj_left' h rfl

theorem append_right_injective (s : List α) : Injective (λ t => s ++ t) :=
  λ _ _ => append_left_cancel

-- attribute [-simp] append_right_inj
theorem X.append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  (append_right_injective s).eq_iff

theorem append_left_injective (t : List α) : Injective (λ s => s ++ t) :=
  λ _ _ => append_right_cancel

-- attribute [-simp] append_left_inj
theorem X.append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  (append_left_injective t).eq_iff

-- attribute [-simp] map_eq_append_split
set_option linter.unusedVariables false in
theorem X.map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
    (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
  ADMIT

/-! ### replicate/repeat -/

-- Note: `replicate` is called `repeat` in Lean 3 and has flipped arguments.

-- SKIP TRIV
-- attribute [-simp] replicate_succ
@[simp] theorem X.replicate_succ (a : α) (n) : replicate (n + 1) a = a :: replicate n a := rfl

-- attribute [-simp] mem_replicate
@[simp] theorem X.mem_replicate {a b : α} {n} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a := by
  induction n <;>
    simp_all only [not_mem_nil, false_and, ne_eq, replicate, mem_cons, Nat.succ_ne_zero,
                   not_false_iff, true_and, or_iff_left_iff_imp, and_imp, implies_true]

-- attribute [-simp] eq_of_mem_replicate
theorem X.eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a :=
  (mem_replicate.1 h).2

theorem eq_replicate_of_mem {a : α} {l : List α} : (∀ b, b ∈ l → b = a) → l = replicate l.length a := λ H =>
  match l with
  | [] => rfl
  | b :: l => by have ⟨H₁, H₂⟩ := forall_mem_cons.1 H; unfold length replicate; congr; exact eq_replicate_of_mem H₂

theorem eq_replicate' {a : α} {l : List α} : l = replicate l.length a ↔ ∀ b, b ∈ l → b = a :=
  ⟨λ h => h.symm ▸ λ _ => eq_of_mem_replicate, eq_replicate_of_mem⟩

theorem eq_replicate {a : α} {n} {l : List α} : l = replicate n a ↔ length l = n ∧ ∀ b, b ∈ l → b = a :=
  ⟨λ h => h.symm ▸ ⟨length_replicate _ _, λ _ => eq_of_mem_replicate⟩,
   λ ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

theorem replicate_add (a : α) (m n) : replicate (m + n) a = replicate m a ++ replicate n a :=
  ADMIT

theorem replicate_subset_singleton (a : α) (n) : replicate n a ⊆ [a] :=
  λ _ h => mem_singleton.2 (eq_of_mem_replicate h)

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a :=
  ADMIT

@[simp] theorem map_const (l : List α) (b : β) : map (λ _ => b) l = replicate l.length b := by
  induction l with
  | nil => rfl
  | cons => simp only [*, replicate, map]; congr

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (λ _ => b₂) l) :
  b₁ = b₂ := by
  rw [map_const] at h; exact eq_of_mem_replicate h

@[simp] theorem map_replicate (f : α → β) (a : α) (n) : map f (replicate n a) = replicate n (f a) := by
  induction n <;> simp only [*, replicate, map]

@[simp] theorem tail_replicate (a : α) (n) : tail (replicate n a) = replicate n.pred a := by
  cases n <;> rfl

@[simp] theorem join_replicate_nil (n : Nat) : join (replicate n []) = @nil α := by
  induction n <;> simp only [*, join, append_nil]

theorem replicate_left_injective {n : Nat} (hn : n ≠ 0) :
    Injective (λ a : α => replicate n a) :=
  λ _ _ h => (eq_replicate.1 h).2 _ $ mem_replicate.2 ⟨hn, rfl⟩

@[simp] theorem replicate_left_inj' {a b : α} :
  ∀ {n}, replicate n a = replicate n b ↔ n = 0 ∨ a = b := by
  intro n; induction n <;>
    simp_all only [replicate, true_or, cons.injEq, Nat.succ_ne_zero, false_or,
    and_iff_left_iff_imp, or_true, implies_true]

theorem replicate_right_injective (a : α) : Injective (λ n => replicate n a) :=
  ADMIT

@[simp] theorem replicate_right_inj {a : α} {n m : Nat} :
    replicate n a = replicate m a ↔ n = m :=
  (replicate_right_injective a).eq_iff

/-! ### pure -/

@[simp]
theorem mem_pure {α} (x y : α) :
    x ∈ (pure y : List α) ↔ x = y := by
  simp only [pure, mem_cons, not_mem_nil, or_false, iff_self]

/-! ### bind -/

instance : Bind List where
  bind l f := List.bind l f

-- SKIP TRIV
@[simp] theorem bind_eq_bind {α β} (f : α → List β) (l : List α) :
    l >>= f = l.bind f := rfl

theorem bind_append (f : α → List β) (l₁ l₂ : List α) :
  (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
  append_bind _ _ _

@[simp] theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)

@[simp] theorem bind_singleton' (l : List α) : l.bind (λ x => [x]) = l := by
  induction l <;> simp_all only [List.bind, join, cons_append, nil_append]

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind (λ x => [f x]) := by
  apply Eq.trans; rw [← bind_singleton' l, bind_map]; rfl

theorem bind_assoc {α β γ : Type u} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind (λ x => (f x).bind g) :=
  ADMIT

/-! ### concat -/

-- SKIP TRIV
@[simp] theorem concat_nil (a : α) : concat [] a = [a] := rfl

-- SKIP TRIV
@[simp] theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b := rfl

-- attribute [-simp] concat_eq_append
@[simp] theorem X.concat_eq_append (a : α) (l : List α) : concat l a = l ++ [a] := by
  induction l <;> simp only [*, concat, nil_append, cons_append]

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ :=
  λ h => by rw [concat_eq_append, concat_eq_append] at h; exact append_right_cancel h

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b :=
  λ h => by rw [concat_eq_append, concat_eq_append] at h; exact head_eq_of_cons_eq (append_left_cancel h)

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by
  simp only [concat_eq_append, ne_eq, X.append_eq_nil, and_false, not_false_iff]

attribute [simp] append_assoc

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by
  simp only [concat_eq_append, append_assoc, cons_append, nil_append]

attribute [-simp] length_concat
theorem X.length_concat (a : α) (l : List α) : length (concat l a) = .succ (length l) := by
  simp only [List.concat_eq_append, length_append, length_cons, length_nil]

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by
  simp only [concat_eq_append, append_assoc]

/-! ### reverse -/

-- SKIP TRIV
attribute [-simp] reverse_nil
@[simp] theorem X.reverse_nil : reverse (@nil α) = [] := rfl

attribute [-simp] reverse_cons
@[simp] theorem X.reverse_cons (a : α) (l : List α) : reverse (a::l) = reverse l ++ [a] :=
  ADMIT

-- Note: reverse_core is called reverseAux in Lean 4.
@[simp]
theorem reverse_core_eq (l₁ l₂ : List α) : reverseAux l₁ l₂ = reverse l₁ ++ l₂ := by
  induction l₁ generalizing l₂ <;> [rfl, (simp only [*, reverseAux, reverse_cons, append_assoc]; rfl)]

theorem reverse_cons' (a : α) (l : List α) : reverse (a::l) = concat (reverse l) a := by
  simp only [X.reverse_cons, concat_eq_append]

-- SKIP TRIV
@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] := rfl

attribute [-simp] reverse_append
@[simp] theorem X.reverse_append (s t : List α) : reverse (s ++ t) = (reverse t) ++ (reverse s) := by
  induction s with
  | nil => rw [nil_append, reverse_nil, append_nil]
  | cons => simp only [*, cons_append, reverse_cons, append_assoc]

-- attribute [-simp] reverse_concat
theorem X.reverse_concat (l : List α) (a : α) : reverse (concat l a) = a :: reverse l := by
  rw [concat_eq_append, reverse_append, reverse_singleton, singleton_append]

attribute [-simp] reverse_reverse
@[simp] theorem X.reverse_reverse (l : List α) : reverse (reverse l) = l := by
  induction l <;> [rfl, (simp only [*, reverse_cons, reverse_append]; rfl)]

@[simp] theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse

@[simp] theorem reverse_injective {α : Type u} : Injective (@reverse α) :=
  reverse_involutive.injective

@[simp] theorem reverse_surjective {α : Type u} : Surjective (@reverse α) :=
  reverse_involutive.surjective

@[simp] theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective


@[simp] theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  reverse_injective.eq_iff

theorem reverse_eq_iff {l l' : List α} :
  l.reverse = l' ↔ l = l'.reverse :=
  reverse_involutive.eq_iff

@[simp] theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] :=
  @reverse_inj _ l []

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  simp only [concat_eq_append, reverse_cons, reverse_reverse]

attribute [-simp] length_reverse
@[simp] theorem X.length_reverse (l : List α) : length (reverse l) = length l := by
  induction l <;> [rfl, simp only [*, reverse_cons, length_append, length]]

theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) := by
  induction l <;> [rfl, simp only [*, map, reverse_cons, map_append]]

theorem map_reverse_core (f : α → β) (l₁ l₂ : List α) :
  map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverse_core_eq, map_append, map_reverse]

attribute [-simp] mem_reverse
@[simp] theorem X.mem_reverse {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l := by
  induction l <;> [rfl, simp only [*, reverse_cons, mem_append, mem_cons, not_mem_nil, or_comm, false_or, iff_self]]

@[simp] theorem reverse_replicate (a : α) (n) : reverse (replicate n a) = replicate n a :=
  ADMIT

/-! ### empty -/

theorem empty_iff_eq_nil {l : List α} : Empty l ↔ l = [] := by
  cases l <;> simp only [Empty, iff_self]

/-! ### init -/

@[simp] theorem length_init : ∀ (l : List α), length (init l) = length l - 1
  | [] => rfl
  | [_] => rfl
  | (_ :: b :: l) => by
    rw [init] <;>
      simp only [length_cons, length_init (b :: l), Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

/-! ### last -/

@[simp] theorem last_cons {a : α} {l : List α} :
  ∀ (h : l ≠ nil), last (a :: l) (cons_ne_nil a l) = last l h := by
  induction l <;> intros <;> [contradiction, rfl]

@[simp] theorem last_append_singleton {a : α} (l : List α) :
  last (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  induction l <;> try solve | rfl
  simp only [cons_append, last_cons (λ H => cons_ne_nil _ _ (append_eq_nil.1 H).2), *]

theorem last_append (l₁ l₂ : List α) (h : l₂ ≠ []) :
  last (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = last l₂ h := by
  induction l₁ <;>
    simp only [*, nil_append, cons_append, ne_eq, X.append_eq_nil, and_false, not_false_iff, last_cons, h]

theorem last_concat {a : α} (l : List α) : last (concat l a) (concat_ne_nil a l) = a := by
  simp only [concat_eq_append, last_append_singleton]

-- SKIP TRIV
@[simp] theorem last_singleton (a : α) : last [a] (cons_ne_nil a []) = a := rfl

-- SKIP TRIV
@[simp] theorem last_cons_cons (a₁ a₂ : α) (l : List α) :
  last (a₁::a₂::l) (cons_ne_nil _ _) = last (a₂::l) (cons_ne_nil a₂ l) := rfl

theorem init_append_last : ∀ {l : List α} (h : l ≠ []), init l ++ [last l h] = l
  | [], h => absurd rfl h
  | [_], h => rfl
  | _ :: _ :: _, h => by
    rw [init, cons_append, last_cons] <;> try exact cons_ne_nil _ _
    congr
    exact init_append_last (cons_ne_nil _ _)

theorem last_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ := by
  subst h₃; rfl

theorem last_mem : ∀ {l : List α} (h : l ≠ []), last l h ∈ l
  | []         , h => absurd rfl h
  | [a]        , h => .head _
  | a :: b :: l, h => .tail _ (by rw [last_cons_cons]; exact last_mem _ )

theorem last_replicate_succ (a m : Nat) :
  (replicate m.succ a).last (ne_nil_of_length_eq_succ
  (show (replicate m.succ a).length = m.succ by rw [length_replicate])) = a := by
  induction m <;> simp_all only [replicate, ne_eq, last]

/-! ### last' -/

@[simp] theorem last'_is_none :
  ∀ {l : List α}, (last' l).isNone ↔ l = []
  | [] => by simp only [last', Option.isNone_none, iff_self]
  | [a] => by simp only [last', Option.isNone_some, iff_self]
  | _ :: b :: l => by simp only [last', @last'_is_none _ (b :: l), iff_self]

@[simp] theorem last'_is_some : ∀ {l : List α}, l.last'.isSome ↔ l ≠ []
  | [] => by simp only [last', Option.isSome_none, ne_eq, not_true, iff_self]
  | [a] => by simp only [last', Option.isSome_some, ne_eq, not_false_iff, iff_self]
  | _ :: b :: l => by simp only [last', @last'_is_some _ (b :: l), ne_eq, not_false_iff, iff_self]

theorem mem_last'_eq_last : ∀ {l : List α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
  | [_], _, _ => by simp_all only [last', Option.mem_some, ne_eq, last, exists_prop, not_false_iff, and_self]
  | a :: b :: l, x, hx => by
    rw [last'] at hx
    rcases mem_last'_eq_last hx with ⟨_, _⟩
    exists cons_ne_nil _ _
    exact cons_ne_nil _ _

theorem last'_eq_last_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.last' = some (l.last h)
  | [], h => (h rfl).elim
  | [a], _ => by unfold last; unfold last'; rfl
  | _ :: b :: l, _ => @last'_eq_last_of_ne_nil _ (b::l) (cons_ne_nil _ _)

theorem mem_last'_cons {x y : α} : ∀ {l : List α} (_ : x ∈ l.last'), x ∈ (y :: l).last'
  | []    , _ => by contradiction
  | (_ :: _), h => h

theorem mem_of_mem_last' {l : List α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
  let ⟨_, h₂⟩ := mem_last'_eq_last ha; h₂.symm ▸ last_mem _

theorem init_append_last' : ∀ {l : List α} {a}, a ∈ l.last' → init l ++ [a] = l
  | [a]          , _, ha => by simp_all only [last', Option.mem_some]; rfl
  | (a :: b :: l), c, hc => by
    rw [last'] at hc
    rw [init, cons_append, init_append_last' (l := b :: l)]
    all_goals simp only [hc, imp_self]

theorem ilast_eq_last' [Inhabited α] : ∀ l : List α, l.ilast = l.last'.iget
  | [] => by simp only [ilast, Option.iget, last']
  | [a] => by rfl
  | [_, _] => by rfl
  | [_, _, _] => by rfl
  | (_ :: _ :: c :: l) => by simp only [ilast, ilast_eq_last' (c :: l), Option.iget, last']

@[simp] theorem last'_append_cons : ∀ (l₁ : List α) (a : α) (l₂ : List α),
  last' (l₁ ++ a :: l₂) = last' (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | _ :: c :: l₁, a, l₂ => by
    rw [cons_append, cons_append, last', ← cons_append, last'_append_cons (c :: l₁)]
    all_goals simp only [imp_self]

-- SKIP TRIV
@[simp] theorem last'_cons_cons (x y : α) (l : List α) :
  last' (x :: y :: l) = last' (y :: l) := rfl

theorem last'_append_of_ne_nil (l₁ : List α) : ∀ {l₂ : List α} (_ : l₂ ≠ []),
  last' (l₁ ++ l₂) = last' l₂
  | b :: l₂, _ => last'_append_cons l₁ b l₂

theorem last'_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.last') :
  x ∈ (l₁ ++ l₂).last' := by
  cases l₂ <;> [contradiction, (rw [last'_append_cons]; exact h)]

/-! ### head(') and tail -/

-- Note: Lean 3 head is Lean 4 ihead.

theorem head_eq_head' [Inhabited α] (l : List α) : ihead l = (head' l).iget := by
  cases l <;> rfl

theorem mem_of_mem_head' {x : α} : ∀ {l : List α}, x ∈ l.head' → x ∈ l
  | a :: l, h => by simp_all only [head', Option.mem_some, mem_cons, true_or]

-- SKIP TRIV
attribute [-simp] head_cons
@[simp] theorem X.head_cons [Inhabited α] (a : α) (l : List α) : head' (a::l) = a := rfl

-- SKIP TRIV
attribute [-simp] tail_nil
@[simp] theorem X.tail_nil : tail (@nil α) = [] := rfl

-- SKIP TRIV
attribute [-simp] tail_cons
@[simp] theorem X.tail_cons (a : α) (l : List α) : tail (a::l) = l := rfl

@[simp] theorem head_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
  ihead (s ++ t) = ihead s := by
  cases s <;> [contradiction, rfl]

theorem head'_append {s t : List α} {x : α} (h : x ∈ s.head') :
  x ∈ (s ++ t).head' := by
  cases s <;> [contradiction, exact h]

theorem head'_append_of_ne_nil : ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []),
  head' (l₁ ++ l₂) = head' l₁ := by
  intro l₁ _ _; cases l₁ <;> [contradiction, rfl]

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
  tail (l ++ [a]) = tail l ++ [a] := by
  induction l <;> [contradiction, rw [tail, cons_append, tail]]

theorem cons_head'_tail : ∀ {l : List α} {a : α} (_ : a ∈ head' l), a :: tail l = l
  | _ :: _, _, _ => by simp_all only [head', Option.mem_spec, Option.some.injEq, X.tail_cons]

theorem head_mem_head' [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), ihead l ∈ head' l
  | _ :: _, _ => by simp_all only [ne_eq, not_false_iff, ihead, head', Option.mem_spec]

theorem cons_head_tail [Inhabited α] {l : List α} (h : l ≠ []) : (ihead l)::(tail l) = l :=
  cons_head'_tail (head_mem_head' h)

end List
