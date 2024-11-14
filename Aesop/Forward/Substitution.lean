/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.PremiseIndex
import Aesop.RulePattern

namespace Aesop

open Lean

set_option linter.missingDocs true

set_option linter.missingDocs false in
/-- A substitution maps premise indices to the instantiations of the
corresponding premises. We represent substitutions as arrays with one element
for each premise index. Hence, a substitution for a rule `r` must have size
`r.numPremiseIndexes`. -/
structure Substitution where
  toArray : Array (Option Expr)
  deriving BEq, Hashable, Inhabited

namespace Substitution

/-- The empty substitution for a rule with the given number of premise
indexes. -/
def empty (numPremiseIndexes : Nat) : Substitution := Id.run do
  return ⟨mkArray numPremiseIndexes none⟩

/-- Insert the mapping `pi ↦ inst` into the substitution `s`. Precondition: `pi`
is in the domain of `s`. -/
def insert (pi : PremiseIndex) (inst : Expr) (s : Substitution) :
    Substitution :=
  ⟨s.toArray.set! pi.toNat inst ⟩

/-- Get the instantiation associated with premise `pi` in `s`. Precondition:
`pi` is in the domain of `s`. -/
def find? (pi : PremiseIndex) (s : Substitution) : Option Expr :=
  s.toArray[pi.toNat]!

instance : ToMessageData Substitution where
  toMessageData s :=
    let xs := s.toArray.filterMap id |>.mapIdx (λ i e => m!"{i} ↦ {e}") |>.toList
    .bracket "{" (.joinSep xs ", ") "}"

/-- Merge two substitutions. Precondition: the substitutions are compatible, so
they must have the same size and if `s₁[x]` and `s₂[x]` are both defined, they
must be the same value. -/
def mergeCompatible (s₁ s₂ : Substitution) : Substitution := Id.run do
  assert! s₁.toArray.size == s₂.toArray.size
  let mut result := s₁
  for h : i in [:s₂.toArray.size] do
    let e? := s₂.toArray[i]
    if let some e := e? then
      assert! let r := s₁.find? ⟨i⟩; r.isNone || r == some e
      if s₁.toArray[i]!.isNone then
        result := result.insert ⟨i⟩ e
  return result

/-- Returns `true` if any expression in the codomain of `s` contains `hyp`. -/
def containsHyp (hyp : FVarId) (s : Substitution) : Bool :=
  s.toArray.any λ
    | none => false
    | some e => e.containsFVar hyp

end Substitution

namespace RulePatternInstantiation

/-- Convert a rule pattern instantiation to a substitution. `pat` is the rule
pattern that was instantiated and `numPremiseIndexes` is the rule to which this
pattern belongs. -/
def toSubstitution (pat : RulePattern) (numPremiseIndexes : Nat)
    (patInst : RulePatternInstantiation) :
    Except String Substitution := do
  let mut subst := .empty numPremiseIndexes
  for i in pat.boundPremises do
    let some inst ← pat.getInstantiation patInst i
      | throw s!"pattern instantiation {patInst.toArray} does not contain an instantiation for premise {i}"
    subst := subst.insert ⟨i⟩ inst
  return subst

end Aesop.RulePatternInstantiation
