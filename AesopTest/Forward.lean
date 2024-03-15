/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true
set_option pp.mvars false

open Aesop Lean Lean.Meta Lean.Elab.Tactic

/-! # Unit tests for the MetaM tactic that implements forward rules -/

syntax (name := forward) "t_forward " ident (" [" ident* "]")? : tactic
syntax (name := elim)    "t_elim "    ident (" [" ident* "]")? : tactic

def forwardTac (goal : MVarId) (id : Ident) (immediate : Option (Array Syntax))
    (clear : Bool) (md : TransparencyMode) : MetaM (List MVarId) := do
  let userName := id.getId
  let ldecl ← getLocalDeclFromUserName userName
  let immediate ← RuleBuilder.getImmediatePremises ldecl.type none md
    (immediate.map (·.map (·.getId)))
  let (goal, _) ←
    RuleTac.applyForwardRule goal (mkFVar ldecl.fvarId) none ∅ immediate clear
      md (maxDepth? := none) |>.run
  return [goal.mvarId]

@[tactic forward]
def evalForward : Tactic
  | `(tactic| t_forward $t:ident $[[ $immediate:ident* ]]?) =>
    liftMetaTactic (forwardTac · t immediate (clear := false) .default)
  | _ => unreachable!

@[tactic elim]
def evalElim : Tactic
  | `(tactic| t_elim $t:ident $[[ $immediate:ident* ]]?) =>
    liftMetaTactic (forwardTac · t immediate (clear := true) .default)
  | _ => unreachable!

example (rule : (a : α) → (b : β) → γ) (h₁ : α) (h₂ : β) : γ := by
  t_forward rule [a b]
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₁' : P a) (h₂ : Q a) (h₃ : P b) (h₄ : Q c) : R a := by
  t_forward rule [p q]
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₁' : P a) (h₂ : Q a) (h₃ : P b) (h₄ : Q c) : R a := by
  t_forward rule
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₂ : P b) : (Q a → R a) × (Q b → R b) := by
  t_forward rule [p]
  exact (by assumption, by assumption)

example (rule : ∀ α β, α ∧ β → α) (h : P ∧ Q ∧ R) : P := by
  t_elim rule
  assumption

/-! # Tests for the `forward` and `saturate` tactics -/

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
  have fwd : γ₁ ∧ γ₂ := r₁ a b
  have fwd_1 : δ₁ ∧ δ₂ := r₂ a
-/
#guard_msgs in
example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  saturate? [*]
  guard_hyp fwd : γ₁ ∧ γ₂
  guard_hyp fwd_1 : δ₁ ∧ δ₂
  aesop

/--
info: Try this:
  have fwd : β := h₁ h₃
  have fwd_1 : γ := h₂ fwd
-/
#guard_msgs in
example {α β γ : Prop} (h₁ : α → β) (h₂ : β → γ) (h₃ : α) : γ := by
  saturate? [*]
  guard_hyp fwd : β
  guard_hyp fwd_1 : γ
  assumption

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
  have fwd : β := h₁ h₄
  have fwd_1 : γ := h₂ h₄
---
error: unsolved goals
α β γ δ : Prop
h₁ : α → β
h₂ : α → γ
h₃ : β → γ → δ
h₄ : α
fwd : β
fwd_1 : γ
⊢ δ
-/
#guard_msgs in
example {α β γ δ : Prop} (h₁ : α → β) (h₂ : α → γ) (h₃ : β → γ → δ) (h₄ : α) : δ := by
  saturate? 1 [*]

axiom A : Type
axiom B : Type
axiom C : Type

@[aesop safe forward]
axiom ab : A → B

@[aesop norm forward]
axiom bc : B → C

/--
info: Try this:
  have fwd : B := ab a
  have fwd_1 : C := bc fwd
-/
#guard_msgs in
noncomputable example : A → C := by
  intro a
  saturate?
  guard_hyp fwd : B
  guard_hyp fwd_1 : C
  exact fwd_1

/-! # Tests for Aesop's forward rules -/

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
