import Aesop

set_option aesop.check.all true

theorem eq_iff_beq_true [DecidableEq α] {a b : α} : a = b ↔ ((a == b) = true) :=
⟨decide_eq_true, of_decide_eq_true⟩

theorem neq_iff_beq_false [DecidableEq α] {a b : α} : a ≠ b ↔ ((a == b) = false) :=
⟨decide_eq_false, of_decide_eq_false⟩

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p :=
⟨of_decide_eq_true, decide_eq_true⟩

theorem decide_eq_false_iff_not (p : Prop) [Decidable p] : (decide p = false) ↔ ¬ p :=
⟨of_decide_eq_false, decide_eq_false⟩

def proof_irrel := @proofIrrel
def congr_fun := @congrFun
def congr_arg := @congrArg

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := by
  aesop

-- TODO How to use a lemma like this? Maybe this is a nice example of e-matching.
theorem cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := by
  aesop

-- TODO make this a norm lemma?
theorem Ne.def (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

-- TODO heq refl default tactic
theorem heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a = a') → (h₂ : Eq.rec (motive := fun a _ => φ a) p₁ e = p₂) → HEq p₁ p₂
| rfl, rfl => HEq.rfl

theorem heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ => φ a) p₂ e) → HEq p₁ p₂
| rfl, rfl => HEq.rfl

theorem of_heq_true (h : HEq a True) : a := of_eq_true (eq_of_heq h)

def And.elim (f : a → b → α) (h : a ∧ b) : α := by
  aesop

theorem And.symm : a ∧ b → b ∧ a := by
  aesop

-- TODO automatic cases on or in hyp (needs per-hyp rules)
theorem Or.myelim {a b c : Prop} (h₁ : a → c) (h₂ : b → c) (h : a ∨ b) : c := by
  aesop (add safe cases Or)

-- TODO make normalisation a fixpoint loop?
-- TODO deal with negation
-- TODO use hyps in the context by default
theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := by
  show ((a ∨ (a → False)) → False) → False
  exact fun H => H (Or.inr fun h => H (Or.inl h))

theorem Or.symm (h : a ∨ b) : b ∨ a := by
  cases h <;> aesop

-- TODO use iff in the context as norm rule?
-- TODO allow local hyps to be added as norm simp rules
def Iff.elim (f : (a → b) → (b → a) → c) (h : a ↔ b) : c :=
  f h.mp h.mpr
  -- by aesop (norm [h (builder simp)])

-- TODO add Iff.intro as default rule
theorem iff_comm : (a ↔ b) ↔ (b ↔ a) := by
  aesop (add safe Iff.intro)

-- TODO don't do contextual simp for all hyps by default (so this should fail)
theorem Eq.to_iff : a = b → (a ↔ b) := by
  aesop

theorem neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

theorem of_iff_true (h : a ↔ True) : a := by aesop

theorem not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

theorem iff_true_intro (h : a) : a ↔ True := by aesop

theorem iff_false_intro (h : ¬a) : a ↔ False := by aesop

theorem not_iff_false_intro (h : a) : ¬a ↔ False := by aesop

theorem not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

theorem forall_congr_iff {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    (∀ x, p x) ↔ (∀ x, q x) := by aesop

theorem imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) := by aesop

-- TODO Iff elim
theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
(imp_congr_left h₁).trans (imp_congr_right h₂)

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := by
  aesop (add safe imp_congr_ctx)

theorem Not.intro {a : Prop} (h : a → False) : ¬a := by aesop

-- TODO try False-elim with low priority if we have a hyp X → False in the
-- context.
def Not.elim (h : ¬a) (ha : a) : α := by aesop

theorem not_true : ¬True ↔ False := by aesop

theorem not_false_iff : ¬False ↔ True := by aesop

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := by aesop

theorem ne_self_iff_false (a : α) : a ≠ a ↔ False := by aesop

theorem eq_self_iff_true (a : α) : a = a ↔ True := by aesop

theorem heq_self_iff_true (a : α) : HEq a a ↔ True := iff_true_intro HEq.rfl

theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

theorem not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

theorem eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

theorem and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

theorem and_comm : a ∧ b ↔ b ∧ a := ⟨And.symm, And.symm⟩

theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

theorem and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := by
  rw [← and_assoc, ← and_assoc, @and_comm a b]
  exact Iff.rfl

theorem and_iff_left (hb : b) : a ∧ b ↔ a := ⟨And.left, fun ha => ⟨ha, hb⟩⟩

theorem and_iff_right (ha : a) : a ∧ b ↔ b := ⟨And.right, fun hb => ⟨ha, hb⟩⟩

theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha
theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := Or.imp f id

theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := Or.imp id f

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
⟨Or.imp h₁.1 h₂.1, Or.imp h₁.2 h₂.2⟩

theorem or_comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

theorem Or.resolve_left (h : a ∨ b) (na : ¬a) : b := h.elim na.elim id

theorem Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.resolve_right (h : a ∨ b) (nb : ¬b) : a := h.elim id nb.elim

theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

open Or in
theorem or_assoc {a b c} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
⟨fun | inl (inl h) => inl h
     | inl (inr h) => inr (inl h)
     | inr h => inr (inr h),
 fun | inl h => inl (inl h)
     | inr (inl h) => inl (inr h)
     | inr (inr h) => inr h⟩

theorem or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by
  rw [← or_assoc, ← or_assoc, @or_comm a b]
  exact Iff.rfl

theorem not_or_intro : (na : ¬a) → (nb : ¬b) → ¬(a ∨ b) := Or.myelim

theorem not_or (p q) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨fun H => ⟨mt Or.inl H, mt Or.inr H⟩, fun ⟨hp, hq⟩ pq => pq.elim hp hq⟩

theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
⟨fun h => h₁.symm.trans $ h.trans h₂, fun h => h₁.trans $ h.trans h₂.symm⟩

@[simp] theorem imp_true_iff : (α → True) ↔ True := iff_true_intro fun _ => ⟨⟩

@[simp] theorem false_imp_iff : (False → a) ↔ True := iff_true_intro False.elim

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

theorem ExistsUnique.intro {p : α → Prop} (w : α)
  (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

theorem ExistsUnique.unique {p : α → Prop} (h : ∃! x, p x)
  {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
let ⟨x, hx, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

theorem Exists.imp {p q : α → Prop} (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
| ⟨a, ha⟩ => ⟨a, h a ha⟩

theorem exists_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

theorem exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
exists_congr fun x => and_congr (h _) $ forall_congr_iff λ y => imp_congr_left (h _)

theorem forall_not_of_not_exists {p : α → Prop} (hne : ¬∃ x, p x) (x) : ¬p x | hp => hne ⟨x, hp⟩

instance forall_prop_decidable {p} (P : p → Prop)
  [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p
  then decidable_of_decidable_of_iff ⟨λ h2 _ => h2, λ al => al h⟩
  else isTrue (λ h2 => absurd h2 h)

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨λ h => h a' rfl, λ h a e => e.symm ▸ h⟩

theorem forall_and_distrib {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h => ⟨λ x => (h x).left, λ x => (h x).right⟩, λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

def Decidable.by_cases := @byCases
def Decidable.by_contradiction := @byContradiction

theorem Decidable.not_and [Decidable p] [Decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := not_and_iff_or_not _ _

@[inline] def Or.by_cases [Decidable p] (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
if hp : p then h₁ hp else h₂ (h.resolve_left hp)

@[inline] def Or.by_cases' [Decidable q] (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
if hq : q then h₂ hq else h₁ (h.resolve_right hq)

theorem Exists.nonempty {p : α → Prop} : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

theorem ite_id [h : Decidable c] {α} (t : α) : (if c then t else t) = t := by cases h <;> rfl

@[simp] theorem if_true {h : Decidable True} (t e : α) : (@ite α True h t e) = t :=
if_pos trivial

@[simp] theorem if_false {h : Decidable False} (t e : α) : (@ite α False h t e) = e :=
if_neg not_false

/-- Universe lifting operation -/
structure ulift.{r, s} (α : Type s) : Type (max s r) :=
up :: (down : α)

namespace ulift
/- Bijection between α and ulift.{v} α -/
theorem up_down {α : Type u} : ∀ (b : ulift.{v} α), up (down b) = b
| up a => rfl

theorem down_up {α : Type u} (a : α) : down (up.{v} a) = a := rfl
end ulift

/-- Universe lifting operation from Sort to Type -/
structure plift (α : Sort u) : Type u :=
up :: (down : α)

namespace plift
/- Bijection between α and plift α -/
theorem up_down : ∀ (b : plift α), up (down b) = b
| (up a) => rfl

theorem down_up (a : α) : down (up a) = a := rfl
end plift

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded

-- Below are items ported from mathlib/src/logic/basic.lean

theorem iff_of_eq (e : a = b) : a ↔ b := e ▸ Iff.rfl

def decidable_of_iff (a : Prop) (h : a ↔ b) [D : Decidable a] : Decidable b :=
decidable_of_decidable_of_iff h

/-
Stuff from mathlib's logic/basic.lean.
TODO: import the whole thing.
-/

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
  fun ⟨ha, hb⟩ => Or.rec ha hb⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
Iff.intro (λ h ha hb => h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩ => h ha hb)

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

@[simp] theorem exists_imp_distrib {p : α → Prop} : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
⟨λ h x hpx => h ⟨x, hpx⟩, λ h ⟨x, hpx⟩ => h x hpx⟩

@[simp] theorem exists_false : ¬ (∃a:α, False) := fun ⟨a, h⟩ => h

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨λ ⟨x, hq, hp⟩ => ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩ => ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp [and_comm]

@[simp] theorem exists_eq {a' : α} : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' {a' : α} : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left {p : α → Prop} {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨a, e, h⟩ => e ▸ h, λ h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {p : α → Prop} {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a => and_comm).trans exists_eq_left

@[simp] theorem exists_eq_left' {p : α → Prop} {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

protected theorem decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
Decidable.by_contradiction $ hb ∘ h

theorem not.decidable_imp_symm [Decidable a] : (¬a → b) → ¬b → a := decidable.not_imp_symm

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬ p x) → ¬ ∀ x, p x
| ⟨x, hn⟩, h => hn (h x)

protected theorem Decidable.not_forall {p : α → Prop}
  [Decidable (∃ x, ¬ p x)] [∀ x, Decidable (p x)] : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨not.decidable_imp_symm $ λ nx x => not.decidable_imp_symm (λ h => ⟨x, h⟩) nx,
 not_forall_of_exists_not⟩

@[simp] theorem not_exists {p : α → Prop} : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

open Classical

@[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x := Decidable.not_forall
