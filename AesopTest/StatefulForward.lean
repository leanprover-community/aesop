/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.dev.statefulForward true
set_option aesop.smallErrorMessages true
set_option pp.mvars false

/--
info: Try this:
  have fwd : γ₁ ∧ γ₂ := r₁ a b
  have fwd_1 : δ₁ ∧ δ₂ := r₂ a
---
error: unsolved goals
α : Sort u_1
β : Sort u_2
γ₁ γ₂ δ₁ δ₂ : Prop
a : α
b : β
r₁ : α → β → γ₁ ∧ γ₂
r₂ : α → δ₁ ∧ δ₂
fwd : γ₁ ∧ γ₂
fwd_1 : δ₁ ∧ δ₂
⊢ γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂
-/
#guard_msgs in
example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  saturate? [*]

/--
info: Try this:
  have fwd : β := h₁ h₃
  have fwd_1 : γ := h₂ fwd
---
error: unsolved goals
α β γ : Prop
h₁ : α → β
h₂ : β → γ
h₃ : α
fwd : β
fwd_1 : γ
⊢ γ
-/
#guard_msgs in
example {α β γ : Prop} (h₁ : α → β) (h₂ : β → γ) (h₃ : α) : γ := by
  saturate? [*]

/--
info: Try this:
have fwd : β := h₁ h₃
---
error: unsolved goals
α β γ : Prop
h₁ : α → β
h₂ : β → γ
h₃ : α
fwd : β
⊢ γ
-/
#guard_msgs in
example {α β γ : Prop} (h₁ : α → β) (h₂ : β → γ) (h₃ : α) : γ := by
  forward? [*]

/--
info: Try this:
have fwd : β := h₁ h₃
---
error: unsolved goals
α β γ : Prop
h₁ : α → β
h₂ : β → γ
h₃ : α
fwd : β
⊢ γ
-/
#guard_msgs in
example {α β γ : Prop} (h₁ : α → β) (h₂ : β → γ) (h₃ : α) : γ := by
  saturate? 1 [*]

/--
info: Try this:
  have fwd : β := h₁ h₄
  have fwd_1 : γ := h₂ fwd
---
error: unsolved goals
α β γ δ : Prop
h₁ : α → β
h₂ : β → γ
h₃ : γ → δ
h₄ : α
fwd : β
fwd_1 : γ
⊢ δ
-/
#guard_msgs in
example {α β γ δ : Prop} (h₁ : α → β) (h₂ : β → γ) (h₃ : γ → δ) (h₄ : α) : δ := by
  saturate? 2 [*]

/--
info: Try this:
  have fwd : γ := h₂ h₄
  have fwd_1 : β := h₁ h₄
---
error: unsolved goals
α β γ δ : Prop
h₁ : α → β
h₂ : α → γ
h₃ : β → γ → δ
h₄ : α
fwd : γ
fwd_1 : β
⊢ δ
-/
#guard_msgs in
example {α β γ δ : Prop} (h₁ : α → β) (h₂ : α → γ) (h₃ : β → γ → δ) (h₄ : α) : δ := by
  saturate? 1 [*]

example {P : Nat → Prop} (hP : P 0) (hPn : ∀ n, P n → P (n + 1)) : P 20 := by
  saturate 20 [*]
  assumption

section

axiom A : Type
axiom B : Type
axiom C : Type

@[local aesop safe forward]
axiom ab : A → B

@[local aesop norm forward]
axiom bc : B → C

/--
info: Try this:
have fwd : P := rule P (Q ∧ R) h
-/
#guard_msgs in
example (rule : ∀ α β, α ∧ β → α) (h : P ∧ Q ∧ R) : P := by
  forward? [*]
  guard_hyp fwd : P
  assumption

/--
info: Try this:
  have fwd : B := ab a
  have fwd_1 : C := bc fwd
---
error: unsolved goals
a : A
fwd : B
fwd_1 : C
⊢ C
-/
#guard_msgs in
noncomputable example : A → C := by
  intro a
  saturate?

end

/--
info: Try this:
have fwd : R a b := h₁ a b h₂ h₃
---
error: unsolved goals
α : Sort u_1
β : Sort u_2
a : α
b : β
P Q R : α → β → Prop
h₁ : ∀ (a : α) (b : β), P a b → Q a b → R a b
h₂ : P a b
h₃ : Q a b
fwd : R a b
⊢ R a b
-/
#guard_msgs in
example {P Q R : α → β → Prop} (h₁ : ∀ a b, P a b → Q a b → R a b)
    (h₂ : P a b) (h₃ : Q a b) : R a b := by
  saturate? [h₁]

/--
info: Try this:
have fwd : R a b := h₁ a b h₂ h₄
---
error: unsolved goals
α : Sort u_1
a b : α
P Q R : α → α → Prop
h₁ : ∀ (a b : α), P a b → Q b a → R a b
h₂ : P a b
h₃ : Q a b
h₄ : Q b a
fwd : R a b
⊢ R a b
-/
#guard_msgs in
example {P Q R : α → α → Prop} (h₁ : ∀ a b, P a b → Q b a → R a b)
    (h₂ : P a b) (h₃ : Q a b) (h₄ : Q b a) : R a b := by
  saturate? [*]

/--
error: unsolved goals
α : Sort u_1
a b : α
P Q R : α → α → Prop
h₁ : ∀ (a b : α), P a b → Q b a → R a b
h₂ : P a b
h₃ : Q a b
⊢ R a b
-/
#guard_msgs in
example {P Q R : α → α → Prop} (h₁ : ∀ a b, P a b → Q b a → R a b)
    (h₂ : P a b) (h₃ : Q a b) : R a b := by
  saturate [*]

/--
info: Try this:
have fwd : R b a := h₁ b a h₄ h₃
---
error: unsolved goals
α : Sort u_1
c d a b : α
P Q R : α → α → Prop
h₁ : ∀ (a b : α), P a b → Q b a → R a b
h₂ : P c d
h₃ : Q a b
h₄ : P b a
fwd : R b a
⊢ R b a
-/
#guard_msgs in
example {P Q R : α → α → Prop} (h₁ : ∀ a b, P a b → Q b a → R a b)
    (h₂ : P c d) (h₃ : Q a b) (h₄ : P b a) : R b a := by
  saturate? [*]

/--
info: Try this:
  have fwd : R c c := h₁ c d d c h₂ h₅
  have fwd_1 : R b c := h₁ b a d c h₄ h₅
  have fwd_2 : R b b := h₁ b a a b h₄ h₃
  have fwd_3 : R c b := h₁ c d a b h₂ h₃
---
error: unsolved goals
α : Sort u_1
c d a b : α
P Q R : α → α → Prop
h₁ : ∀ (a b c d : α), P a b → Q c d → R a d
h₂ : P c d
h₃ : Q a b
h₄ : P b a
h₅ : Q d c
fwd : R c c
fwd_1 : R b c
fwd_2 : R b b
fwd_3 : R c b
⊢ R c b
-/
#guard_msgs in
example {P Q R : α → α → Prop} (h₁ : ∀ a b c d, P a b → Q c d → R a d)
    (h₂ : P c d) (h₃ : Q a b) (h₄ : P b a) (h₅ : Q d c) : R c b := by
  saturate? [*]

/--
info: Try this:
  have fwd : S a c := h₁ a b d c h₂ h₃ h₅
  have fwd_1 : S a d := h₁ a b c d h₂ h₃ h₄
---
error: unsolved goals
α : Sort u_1
a b c d : α
P Q R S : α → α → Prop
h₁ : ∀ (a b c d : α), P a b → Q b a → R c d → S a d
h₂ : P a b
h₃ : Q b a
h₄ : R c d
h₅ : R d c
fwd : S a c
fwd_1 : S a d
⊢ S a d
-/
#guard_msgs in
example {P Q R S : α → α → Prop} (h₁ : ∀ a b c d, P a b → Q b a → R c d → S a d)
    (h₂ : P a b) (h₃ : Q b a) (h₄ : R c d) (h₅ : R d c) : S a d := by
  saturate? [*]

/--
info: Try this:
have fwd : R b a := h₁ a b h₂ h₃ h₄
---
error: unsolved goals
α : Sort u_1
a b : α
P : α → Prop
Q R : α → α → Prop
h₁ : ∀ (a b : α), P a → P b → Q a b → R b a
h₂ : P a
h₃ : P b
h₄ : Q a b
fwd : R b a
⊢ Q b a
-/
#guard_msgs in
example {P : α → Prop} {Q R : α → α → Prop}
    (h₁ : ∀ a b, P a → P b → Q a b → R b a)
    (h₂ : P a) (h₃ : P b) (h₄ : Q a b) : Q b a := by
  saturate? [*]

/--
info: Try this:
have fwd : R b a := h₁ a b h₆ h₅ h₄
---
error: unsolved goals
α : Sort u_1
c d a b : α
P : α → Prop
Q R : α → α → Prop
h₁ : ∀ (a b : α), P a → P b → Q a b → R b a
h₂ : P c
h₃ : P d
h₄ : Q a b
h₅ : P b
h₆ : P a
fwd : R b a
⊢ Q b a
-/
#guard_msgs in
example {P : α → Prop} {Q R : α → α → Prop}
    (h₁ : ∀ a b, P a → P b → Q a b → R b a)
    (h₂ : P c) (h₃ : P d) (h₄ : Q a b) (h₅ : P b) (h₆ : P a) : Q b a := by
  saturate? [*]

/--
info: Try this:
  have fwd : R c d := h₁ d c h₃ h₂ h₇
  have fwd_1 : R b a := h₁ a b h₆ h₅ h₄
---
error: unsolved goals
α : Sort u_1
c d a b : α
P : α → Prop
Q R : α → α → Prop
h₁ : ∀ (a b : α), P a → P b → Q a b → R b a
h₂ : P c
h₃ : P d
h₄ : Q a b
h₅ : P b
h₆ : P a
h₇ : Q d c
fwd : R c d
fwd_1 : R b a
⊢ Q b a
-/
#guard_msgs in
example {P : α → Prop} {Q R : α → α → Prop}
    (h₁ : ∀ a b, P a → P b → Q a b → R b a)
    (h₂ : P c) (h₃ : P d) (h₄ : Q a b) (h₅ : P b) (h₆ : P a) (h₇ : Q d c) : Q b a := by
  saturate? [*]

example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  aesop (add safe [forward r₁, forward (immediate := [a]) r₂])

/--
info: Try this:
  have fwd : γ₁ ∧ γ₂ := r₁ a b
  simp_all only [and_self, implies_true, true_and]
  obtain ⟨left, right⟩ := fwd
  have fwd : δ₁ ∧ δ₂ := r₂ a
  simp_all only [and_self, implies_true]
-/
#guard_msgs in
example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  aesop? (add safe [forward r₁, forward (immediate := [a]) r₂])

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  aesop (add safe [destruct r₁, destruct (immediate := [a]) r₂])
    (config := { terminal := true })

example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  aesop (add safe [forward r₁], 90% destruct r₂)

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
α β γ : Prop
h₁ : α
h₂ : β
fwd : γ
⊢ False
-/
#guard_msgs in
example {α β γ : Prop} (h : α → β → γ) (h₁ : α) (h₂ : β) : False := by
  aesop (add norm -1 forward h)
  -- TODO with `safe` instead of `norm`, exposes an error in local rule handling.

section Computation

-- Stateful forward reasoning sees through `reducible` definitions...

abbrev rid (x : α) : α := x

example {P Q : α → Prop} (h₁ : ∀ a, P a → Q a → X) (h₂ : P (rid a)) (h₃ : Q a) : X := by
  saturate [h₁]
  exact fwd

-- ... but not through semireducible ones.

/--
error: unsolved goals
α : Sort _
X : Sort _
a : α
P Q : α → Prop
h₁ : (a : α) → P a → Q a → X
h₂ : P (id a)
h₃ : Q a
⊢ X
-/
#guard_msgs in
example {P Q : α → Prop} (h₁ : ∀ a, P a → Q a → X) (h₂ : P (id a)) (h₃ : Q a) : X := by
  saturate [h₁]

end Computation

namespace Immediate

axiom α : Type
axiom P : α → Prop
axiom Q : α → Prop
axiom R : α → Prop

@[aesop safe forward (immediate := [h₂])]
axiom foo : ∀ a (h₁ : P a) (h₂ : Q a), R a

/--
error: unsolved goals
a : α
h : Q a
fwd : P a → R a
⊢ False
-/
#guard_msgs in
example (h : Q a) : False := by
  saturate

end Immediate

namespace Instance

class Foo (α : Type) : Prop

axiom β : Type

@[aesop safe forward]
axiom foo : ∀ (α : Type) (a : α) [Foo α], β

/--
error: unsolved goals
α : Type
inst✝ : Foo α
a : α
fwd : β
⊢ False
-/
#guard_msgs in
example [Foo α] (a : α) : False := by
  saturate

axiom γ : Type

instance : Foo γ where

/--
error: unsolved goals
c : γ
fwd : β
⊢ False
-/
#guard_msgs in
example (c : γ) : False := by
  saturate

@[aesop safe forward (immediate := [a])]
axiom bar : ∀ α β (a : α) (b : β) [Foo β], γ

/--
error: unsolved goals
α : Sort u_1
a : α
⊢ False
-/
#guard_msgs in
example (a : α) : False := by
  saturate

/--
error: unsolved goals
c : γ
fwd : β
⊢ False
-/
#guard_msgs in
example (c : γ) : False := by
  saturate

end Instance
