/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

-- TODO enable checks once stateful forward reasoning supports script generation

set_option aesop.dev.statefulForward true

/--
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
  saturate [*]

/--
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
  saturate [*]

section

axiom A : Type
axiom B : Type
axiom C : Type

@[local aesop safe forward]
axiom ab : A → B

@[local aesop norm forward]
axiom bc : B → C

/--
error: unsolved goals
a : A
fwd : B
fwd_1 : C
⊢ C
-/
#guard_msgs in
noncomputable example : A → C := by
  intro a
  saturate

end

/--
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
  saturate [h₁]

/--
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
  saturate [*]

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
  saturate [*]

/--
error: unsolved goals
α : Sort u_1
c d a b : α
P Q R : α → α → Prop
h₁ : ∀ (a b c d : α), P a b → Q c d → R a d
h₂ : P c d
h₃ : Q a b
h₄ : P b a
h₅ : Q d c
fwd : R b c
fwd_1 : R c c
fwd_2 : R b b
fwd_3 : R c b
⊢ R c b
-/
#guard_msgs in
example {P Q R : α → α → Prop} (h₁ : ∀ a b c d, P a b → Q c d → R a d)
    (h₂ : P c d) (h₃ : Q a b) (h₄ : P b a) (h₅ : Q d c) : R c b := by
  saturate [*]

/--
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
  saturate [*]

/--
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
  saturate [*]

/--
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
  saturate [*]

/--
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
  saturate [*]
