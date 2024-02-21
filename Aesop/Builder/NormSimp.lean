/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

private def getSimpEntriesFromPropConst (decl : Name) :
    MetaM (Array SimpEntry) := do
  let thms ← ({} : SimpTheorems).addConst decl
  return SimpTheorems.simpEntries thms

private def getSimpEntriesForConst (decl : Name) : MetaM (Array SimpEntry) := do
  let info ← getConstInfo decl
  let mut thms : SimpTheorems := {}
  if (← isProp info.type) then
    thms ← thms.addConst decl
  else if info.hasValue then
    thms ← thms.addDeclToUnfold decl
  return SimpTheorems.simpEntries thms

def RuleBuilderInput.getSimpPrio [Monad m] [MonadError m]
    (input : RuleBuilderInput) : m Nat :=
  match input.extra with
  | .norm penalty =>
    if penalty ≥ 0 then
      return penalty.toNat
    else
      throwError "aesop: simp rules must be given a non-negative integer priority"
  | _ => throwError "aesop: simp builder can only construct 'norm' rules"

def RuleBuilder.simp : RuleBuilder := λ input => do
  if let some decl ← elabGlobalRuleIdent? input.term then
    try {
      let entries ← getSimpEntriesForConst decl
      let prio ← input.getSimpPrio
      let entries := entries.map (updateSimpEntryPriority prio)
      let name :=
        { name := decl, scope := .global, builder := .simp, phase := .norm }
      return .global $ .normSimpRule { name, entries }
    } catch e => {
      throwError "aesop: simp builder: exception while trying to add {decl} as a simp theorem:{indentD e.toMessageData}"
    }
  else
    checkElabRuleTermForSimp input.term (isSimpAll := true) -- TODO (isSimpAll := true) correct?
    return .localNormSimpRule {
      id := ← mkFreshLocalRuleName
      simpTheorem := input.term
    }

end Aesop
