/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

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

def simp : RuleBuilder := λ input => do
  match input.kind with
  | .global decl =>
    try {
      let entries ← getSimpEntriesForConst decl
      return .global $ .globalSimp entries
    } catch e => {
      throwError "aesop: simp builder: exception while trying to add {decl} as a simp theorem:{indentD e.toMessageData}"
    }
  | .«local» fvarUserName goal =>
    goal.withContext do
      let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
      unless ← isProp type do
        throwError "aesop: simp builder: simp rules must be propositions but {fvarUserName} has type{indentExpr type}"
      return .«local» goal (.localSimp fvarUserName)

end Aesop.RuleBuilder
