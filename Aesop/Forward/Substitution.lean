/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.PremiseIndex
import Aesop.RPINF.Basic

namespace Aesop

open Lean Lean.Meta

set_option linter.missingDocs true

set_option linter.missingDocs false in
/-- A substitution maps premise indices to the instantiations of the
corresponding premises. We represent substitutions as arrays with one element
for each premise index. Hence, a substitution for a rule `r` must have size
`r.numPremiseIndexes`. -/
structure Substitution where
  toArray : Array (Option RPINF)
  deriving BEq, Hashable, Inhabited

namespace Substitution

/-- The empty substitution for a rule with the given number of premise
indexes. -/
def empty (numPremiseIndexes : Nat) : Substitution := Id.run do
  return ⟨mkArray numPremiseIndexes none⟩

/-- Insert the mapping `pi ↦ inst` into the substitution `s`. Precondition: `pi`
is in the domain of `s`. -/
def insert (pi : PremiseIndex) (inst : RPINF) (s : Substitution) :
    Substitution :=
  ⟨s.toArray.set! pi.toNat inst ⟩

/-- Get the instantiation associated with premise `pi` in `s`. Precondition:
`pi` is in the domain of `s`. -/
def find? (pi : PremiseIndex) (s : Substitution) : Option RPINF :=
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
    | some e => e.toExpr.containsFVar hyp

/-- Given `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U` and a substitution `σ` for the
arguments `xᵢ`, replace occurrences of `xᵢ` in the body `U` with fresh
metavariables (like `forallMetaTelescope`). Then, for each mapping `xᵢ ↦ tᵢ` in
`σ`, assign `tᵢ` to tthe metavariable corresponding to `xᵢ`. Returns the new
metavariables, their binder infos, the new body and a set containing those
new metavariables that were assigned. -/
def openRuleType (type : Expr) (subst : Substitution) :
    MetaM (Array Expr × Array BinderInfo × Expr × Std.HashSet MVarId) := do
  let (mvars, binfos, body) ← forallMetaTelescopeReducing type
  let mut assigned := ∅
  for h : i in [:mvars.size] do
    if let some inst := subst.find? ⟨i⟩ then
      let mvarId := mvars[i].mvarId!
      -- We use `isDefEq` to make sure that universe metavariables occurring in
      -- the type of `mvarId` are assigned.
      if ← isDefEq (.mvar mvarId) inst.toExpr then
        assigned := assigned.insert mvarId
      else
        throwError "openRuleType: type-incorrect substitution: argument has type '{← mvarId.getType}' but instantiation '{inst}' has type '{← inferType inst.toExpr}'"
  return (mvars, binfos, body, assigned)

/-- Given `rule` of type `∀ (x₁ : T₁) ... (xₙ : Tₙ), U` and a substitution `σ` for
the arguments `xᵢ`, specialise `rule` with the arguments given by `σ`. That is,
construct `U t₁ ... tₙ` where `tⱼ` is `σ(xⱼ)` if `xⱼ ∈ dom(σ)` and is otherwise
a fresh fvar, then λ-abstract the fresh fvars.
-/
def specializeRule (rule : Expr) (subst : Substitution) : MetaM Expr :=
  withNewMCtxDepth do
    forallTelescopeReducing (← inferType rule) λ fvarIds _ => do
      let mut args := Array.mkEmpty fvarIds.size
      let mut remainingFVarIds := Array.mkEmpty fvarIds.size
      for h : i in [:fvarIds.size] do
        if let some inst := subst.find? ⟨i⟩ then
          args := args.push $ some inst.toExpr
        else
          let fvarId := fvarIds[i]
          args := args.push $ some fvarId
          remainingFVarIds := remainingFVarIds.push fvarId
      let result ← mkLambdaFVars remainingFVarIds (← mkAppOptM' rule args)
      return result

end Substitution

/-- Open the type of a rule. If a substitution `σ` is given, this function acts
like `Substitution.openRuleType σ`. Otherwise it acts like
`forallMetaTelescope`. -/
def openRuleType (subst? : Option Substitution) (type : Expr) :
    MetaM (Array Expr × Array BinderInfo × Expr × Std.HashSet MVarId) := do
  match subst? with
  | some subst => do
    subst.openRuleType type
  | none =>
    let (premises, binfos, conclusion) ← forallMetaTelescopeReducing type
    return (premises, binfos, conclusion, ∅)

end Aesop
