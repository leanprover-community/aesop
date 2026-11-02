/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Builder.Basic

public section

open Lean
open Lean.Meta

namespace Aesop

private def getSimpEntriesFromPropConst (decl : Name) :
    MetaM (Array SimpEntry) := do
  let thms ← ({} : SimpTheorems).addConst decl
  return SimpTheorems.simpEntries thms

private def getSimpEntriesForConst (decl : Name) (inv : Bool) :
    MetaM (Array SimpEntry) := do
  let info ← getConstInfo decl
  let mut thms : SimpTheorems := {}
  if (← isProp info.type) then
    thms ← thms.addConst decl (inv := inv)
  else if info.hasValue then
    if inv then
      throwError "aesop: invalid `←` modifier: `{decl}` is a declaration name to be unfolded"
    thms ← thms.addDeclToUnfold decl
  return SimpTheorems.simpEntries thms

def PhaseSpec.getSimpPrio [Monad m] [MonadError m] : PhaseSpec → m Nat
  | .norm info =>
    if info.penalty ≥ 0 then
      return info.penalty.toNat
    else
      throwError "aesop: simp rules must be given a non-negative integer priority"
  | _ => throwError "aesop: simp builder can only construct 'norm' rules"

namespace RuleBuilder

def simpCore (decl : Name) (phase : PhaseSpec) (reverse : Bool) :
    MetaM LocalRuleSetMember :=
  withExceptionTransform (λ msg => m!"aesop: simp builder: exception while trying to add {decl} as a simp theorem:{indentD msg}") do
    let entries ← getSimpEntriesForConst decl reverse
    let prio ← phase.getSimpPrio
    let entries := entries.map (updateSimpEntryPriority prio)
    let name :=
      { name := decl, scope := .global, builder := .simp, phase := .norm }
    return .global $ .normSimpRule { name, entries }

def simp : RuleBuilder := λ input => do
  if let some decl ← elabGlobalRuleIdent? input.term then
    return ← simpCore decl input.phase input.reverse
  checkElabRuleTermForSimp input.term (isSimpAll := true) -- TODO (isSimpAll := true) correct?
    (reverse := input.reverse)
  return .localNormSimpRule {
    id := ← mkFreshId
    simpTheorem := input.term
    reverse := input.reverse
  }

end Aesop.RuleBuilder
