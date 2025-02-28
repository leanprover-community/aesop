/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.LevelIndex
import Aesop.Forward.PremiseIndex
import Aesop.Util.Basic
import AesopPrecomp.RPINF

namespace Aesop

open Lean Lean.Meta

set_option linter.missingDocs true

/-- A substitution for the premises of a rule. Given a rule with type
`∀ (x₁ : T₁) ... (xₙ : Tₙ), U` a substitution is a finite partial map with
domain `{1, ..., n}` that associates an expression with some or all of the
premises. -/
structure Substitution where
  /-- The substitution. -/
  premises : Array (Option RPINF)
  /-- The level substitution implied by the premise substitution. If `e` is the
  elaborated rule expression (with level params replaced by level mvars), and
  `collectLevelMVars (← instantiateMVars e) = [?m₁, ..., ?mₙ]`, then `levels[i]`
  is the level assigned to `?mᵢ`. -/
  levels : Array (Option Level)
  deriving Inhabited

namespace Substitution

instance : BEq Substitution where
  beq s₁ s₂ := s₁.premises == s₂.premises

instance : Hashable Substitution where
  hash s := hash s.premises

instance : Ord Substitution where
  compare s₁ s₂ :=
    compare s₁.premises.size s₂.premises.size |>.then $
    compareArrayLex compare s₁.premises s₂.premises

/-- The empty substitution for a rule with the given number of premise
indexes. -/
def empty (numPremises numLevels : Nat) : Substitution where
  premises := mkArray numPremises none
  levels   := mkArray numLevels   none

/-- Insert the mapping `pi ↦ inst` into the substitution `s`. Precondition: `pi`
is in the domain of `s`. -/
def insert (pi : PremiseIndex) (inst : RPINF) (s : Substitution) :
    Substitution :=
  { s with premises := s.premises.set! pi.toNat inst }

/-- Get the instantiation associated with premise `pi` in `s`. Precondition:
`pi` is in the domain of `s`. -/
def find? (pi : PremiseIndex) (s : Substitution) : Option RPINF :=
  s.premises[pi.toNat]!

/-- Insert the mapping `li ↦ inst` into the substitution `s`. Precondition: `li`
is in the domain of `s` and `inst` is normalised. -/
def insertLevel (li : LevelIndex) (inst : Level) (s : Substitution) :
    Substitution :=
  { s with levels := s.levels.set! li.toNat inst }

/-- Get the instantiation associated with level `li` in `s`. Precondition:
`li` is in the domain of `s`. -/
def findLevel? (li : PremiseIndex) (s : Substitution) : Option Level :=
  s.levels[li.toNat]!

instance : ToMessageData Substitution where
  toMessageData s :=
    let ps := s.premises.filterMap id |>.mapIdx (λ i e => m!"{i} ↦ {e}") |>.toList
    let ls := s.levels.filterMap   id |>.mapIdx (λ i l => m!"{i} ↦ {l}") |>.toList
    .bracket "{" (.joinSep ps ", " ++ " | " ++ .joinSep ls ", ") "}"

/-- Merge two substitutions. Precondition: the substitutions are compatible, so
they must have the same size and if `s₁[x]` and `s₂[x]` are both defined, they
must be the same value. -/
def mergeCompatible (s₁ s₂ : Substitution) : Substitution := Id.run do
  assert! s₁.premises.size == s₂.premises.size
  assert! s₁.levels.size == s₂.levels.size
  let mut result := s₁
  for h : i in [:s₂.premises.size] do
    if let some e := s₂.premises[i] then
      assert! let r := s₁.find? ⟨i⟩; r.isNone || r == some e
      if s₁.premises[i]!.isNone then
        result := result.insert ⟨i⟩ e
  for h : i in [:s₂.levels.size] do
    if let some l := s₂.levels[i] then
      if s₁.levels[i]!.isNone then
        result := result.insertLevel ⟨i⟩ l
  return result

/-- Returns `true` if any expression in the codomain of `s` contains `hyp`. -/
def containsHyp (hyp : FVarId) (s : Substitution) : Bool :=
  s.premises.any λ
    | none => false
    | some e => e.toExpr.containsFVar hyp

/-- Given `e` with type `∀ (x₁ : T₁) ... (xₙ : Tₙ), U` and a substitution `σ`
for the arguments `xᵢ`, replace occurrences of `xᵢ` in the body `U` with fresh
metavariables (like `forallMetaTelescope`). Then, for each mapping `xᵢ ↦ tᵢ` in
`σ`, assign `tᵢ` to the metavariable corresponding to `xᵢ`. Returns the newly
created metavariables (which may be assigned!), their binder infos and the
updated body. -/
def openRuleType (e : Expr) (subst : Substitution) :
    MetaM (Array MVarId × Array BinderInfo × Expr) := do
  let lmvarIds := collectLevelMVars {} (← instantiateMVars e) |>.result
  if subst.levels.size != lmvarIds.size then
    throwError "openRuleType: substitution contains incorrect number of levels. Rule:{indentExpr e}\nSubstitution:{indentD $ toMessageData subst}"
  let type ← inferType e
  let (mvars, binfos, body) ← forallMetaTelescopeReducing type
  let mvarIds := mvars.map (·.mvarId!)
  if subst.premises.size != mvars.size then
    throwError "openRuleType: substitution has incorrect size. Rule:{indentExpr e}\nRule type:{indentExpr type}\nSubstitution:{indentD $ toMessageData subst}"
  for h : i in [:lmvarIds.size] do
    if let some inst := subst.findLevel? ⟨i⟩ then
      assignLevelMVar lmvarIds[i] inst
  for h : i in [:mvarIds.size] do
    if let some inst := subst.find? ⟨i⟩ then
      mvarIds[i].assign inst.toExpr
  return (mvarIds, binfos, body)

/-- Given `rule` of type `∀ (x₁ : T₁) ... (xₙ : Tₙ), U` and a substitution `σ` for
the arguments `xᵢ`, specialise `rule` with the arguments given by `σ`. That is,
construct `U t₁ ... tₙ` where `tⱼ` is `σ(xⱼ)` if `xⱼ ∈ dom(σ)` and is otherwise
a fresh fvar, then λ-abstract the fresh fvars. -/
def specializeRule (rule : Expr) (subst : Substitution) : MetaM Expr :=
  withNewMCtxDepth do
    let lmvarIds := collectLevelMVars {} (← instantiateMVars rule) |>.result
    for h : i in [:lmvarIds.size] do
      if let some l := subst.findLevel? ⟨i⟩ then
        assignLevelMVar lmvarIds[i] l
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

/-- Open the type of a rule `e`. If a substitution `σ` is given, this function
acts like `Substitution.openRuleType σ`. Otherwise it acts like
`forallMetaTelescope`. -/
def openRuleType (subst? : Option Substitution) (e : Expr) :
    MetaM (Array MVarId × Array BinderInfo × Expr) := do
  match subst? with
  | some subst => do
    subst.openRuleType e
  | none =>
    let (premises, binfos, conclusion) ←
      forallMetaTelescopeReducing (← inferType e)
    return (premises.map (·.mvarId!), binfos, conclusion)

end Aesop
