/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.Match
import Aesop.Rule

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- Sets of complete matches for norm/safe/unsafe rules. -/
structure ForwardRuleMatches where
  /-- Complete matches of norm rules. -/
  normMatches   : PHashSet ForwardRuleMatch
  /-- Complete matches of safe rules. -/
  safeMatches   : PHashSet ForwardRuleMatch
  /-- Complete matches of unsafe rules. -/
  unsafeMatches : PHashSet ForwardRuleMatch
  deriving Inhabited

namespace ForwardRuleMatches

/-- Empty `ForwardRuleMatches`. -/
protected def empty : ForwardRuleMatches where
  normMatches := ∅
  safeMatches := ∅
  unsafeMatches := ∅

instance : EmptyCollection ForwardRuleMatches :=
  ⟨.empty⟩

/-- Add a complete match. -/
def insert (m : ForwardRuleMatch) (ms : ForwardRuleMatches) :
    ForwardRuleMatches :=
  match m.rule.name.phase with
  | .norm =>   { ms with normMatches   := ms.normMatches.insert   m }
  | .safe =>   { ms with safeMatches   := ms.safeMatches.insert   m }
  | .unsafe => { ms with unsafeMatches := ms.unsafeMatches.insert m }

/-- Add several complete matches. -/
def insertMany (ms : Array ForwardRuleMatch) (ms' : ForwardRuleMatches) :
    ForwardRuleMatches :=
  ms.foldl (init := ms') λ ms' m => ms'.insert m

/-- Erase a complete match. -/
def erase (m : ForwardRuleMatch) (ms : ForwardRuleMatches) :
    ForwardRuleMatches :=
  match m.rule.name.phase with
  | .norm =>   { ms with normMatches   := ms.normMatches.erase m }
  | .safe =>   { ms with safeMatches   := ms.safeMatches.erase m }
  | .unsafe => { ms with unsafeMatches := ms.unsafeMatches.erase m }

/-- Erase several complete matches. -/
def eraseMany (ms : Array ForwardRuleMatch) (ms' : ForwardRuleMatches) :
    ForwardRuleMatches :=
  ms.foldl (init := ms') λ ms' m => ms'.erase m

/-- Build a `ForwardRuleMatches` structure containing the matches from `ms`. -/
def ofArray (ms : Array ForwardRuleMatch) : ForwardRuleMatches :=
  (∅ : ForwardRuleMatches).insertMany ms

/-- Erase matches containing any of the hypotheses `hs` from `ms`. -/
def eraseHyps (hs : Std.HashSet FVarId) (ms : ForwardRuleMatches) :
    ForwardRuleMatches where
  normMatches   := go ms.normMatches
  safeMatches   := go ms.safeMatches
  unsafeMatches := go ms.unsafeMatches
where
  go (ms : PHashSet ForwardRuleMatch) : PHashSet ForwardRuleMatch :=
    let toErase := ms.fold (init := #[]) λ toErase m =>
      if m.anyHyp hs.contains then toErase.push m else toErase
    toErase.foldl (init := ms) λ ms m => ms.erase m

/-- Erase matches containing the hypothesis `h` from `ms`. -/
def eraseHyp (h : FVarId) (ms : ForwardRuleMatches) : ForwardRuleMatches :=
  ms.eraseHyps {h}

private def foldRules! (ms : PHashSet ForwardRuleMatch)
    (f : ForwardRuleMatch → Option α) (g : σ → α → σ) (init : σ) : σ :=
  have : Inhabited σ := ⟨init⟩
  ms.fold (init := init) λ s m =>
    match f m with
    | none => panic! s!"conversion failed for match of rule {m.rule.name}"
    | some a => g s a

/-- Fold over the norm rules corresponding to the norm rule matches. -/
def foldNormRules (ms : ForwardRuleMatches) (f : σ → NormRule → σ) (init : σ) :
    σ :=
  foldRules! ms.normMatches (·.toNormRule?) f init

/-- Get the norm rules corresponding to the norm rule matches. -/
def normRules (ms : ForwardRuleMatches) : Array NormRule :=
  ms.foldNormRules (init := #[]) (·.push ·)

/-- Fold over the safe rules corresponding to the safe rule matches. -/
def foldSafeRules (ms : ForwardRuleMatches) (f : σ → SafeRule → σ) (init : σ) :
    σ :=
  foldRules! ms.safeMatches (·.toSafeRule?) f init

/-- Get the safe rules corresponding to the safe rule matches. -/
def safeRules (ms : ForwardRuleMatches) : Array SafeRule :=
  ms.foldSafeRules (init := #[]) (·.push ·)

/-- Fold over the unsafe rules corresponding to the unsafe rule matches. -/
def foldUnsafeRules (ms : ForwardRuleMatches) (f : σ → UnsafeRule → σ)
    (init : σ) : σ :=
  foldRules! ms.unsafeMatches (·.toUnsafeRule?) f init

/-- Get the unsafe rules corresponding to the unsafe rule matches. -/
def unsafeRules (ms : ForwardRuleMatches) : Array UnsafeRule :=
  ms.foldUnsafeRules (init := #[]) (·.push ·)

/-- `O(n)` Number of matches in `ms`. -/
def size (ms : ForwardRuleMatches) : Nat :=
  ms.normMatches.fold   (init := 0) (λ n _ => n + 1) +
  ms.safeMatches.fold   (init := 0) (λ n _ => n + 1) +
  ms.unsafeMatches.fold (init := 0) (λ n _ => n + 1)

end ForwardRuleMatches

end Aesop
