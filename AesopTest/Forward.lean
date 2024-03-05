/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true
set_option aesop.smallErrorMessages true

open Aesop Lean Lean.Meta Lean.Elab.Tactic

/-! # Unit tests for the MetaM tactic that implements forward rules -/

syntax (name := forward) "forward " ident (" [" ident* "]")? : tactic
syntax (name := elim)    "elim "    ident (" [" ident* "]")? : tactic

def forwardTac (goal : MVarId) (id : Ident) (immediate : Option (Array Syntax))
    (clear : Bool) (md : TransparencyMode) : MetaM (List MVarId) := do
  let userName := id.getId
  let ldecl ← getLocalDeclFromUserName userName
  let immediate ← RuleBuilder.getImmediatePremises id ldecl.type
    none md (immediate.map (·.map (·.getId)))
  let (goal, _) ←
    RuleTac.applyForwardRule goal (mkFVar ldecl.fvarId) none ∅ immediate clear
      (generateScript := false) md
  return [goal]

@[tactic forward]
def evalForward : Tactic
  | `(tactic| forward $t:ident $[[ $immediate:ident* ]]?) =>
    liftMetaTactic (forwardTac · t immediate (clear := false) .default)
  | _ => unreachable!

@[tactic elim]
def evalElim : Tactic
  | `(tactic| elim $t:ident $[[ $immediate:ident* ]]?) =>
    liftMetaTactic (forwardTac · t immediate (clear := true) .default)
  | _ => unreachable!

example (rule : (a : α) → (b : β) → γ) (h₁ : α) (h₂ : β) : γ := by
  forward rule [a b]
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₁' : P a) (h₂ : Q a) (h₃ : P b) (h₄ : Q c) : R a := by
  forward rule [p q]
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₁' : P a) (h₂ : Q a) (h₃ : P b) (h₄ : Q c) : R a := by
  forward rule
  assumption

example {P Q R : α → Type} (rule : ∀ a (p : P a) (q : Q a), R a)
    (h₁ : P a) (h₂ : P b) : (Q a → R a) × (Q b → R b) := by
  forward rule [p]
  exact (by assumption, by assumption)

example (rule : ∀ α β, α ∧ β → α) (h : P ∧ Q ∧ R) : P := by
  elim rule
  assumption

/-! # End-to-end tests -/

example (a : α) (b : β) (r₁ : (a : α) → (b : β) → γ₁ ∧ γ₂)
    (r₂ : (a : α) → δ₁ ∧ δ₂) : γ₁ ∧ γ₂ ∧ δ₁ ∧ δ₂ := by
  aesop (add safe [forward r₁, forward (immediate := [a]) r₂])

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
