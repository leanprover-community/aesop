/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public meta import Aesop.Util.Unfold

public section

open Lean Lean.Meta Lean.Elab.Tactic

namespace Aesop

private meta def mkToUnfold (ids : Array Ident) :
    MetaM (Std.HashMap Name (Option Name)) := do
  let mut toUnfold : Std.HashMap Name (Option Name) := {}
  for id in (ids : Array Ident) do
    let decl ← resolveGlobalConstNoOverload id
    toUnfold := toUnfold.insert decl (← getUnfoldEqnFor? decl)
  return toUnfold

elab "aesop_unfold " ids:ident+ : tactic => do
  let toUnfold ← mkToUnfold ids
  liftMetaTactic λ goal => do
    match ← unfoldManyTarget (toUnfold[·]?) goal with
    | none => throwTacticEx `aesop_unfold goal "could not unfold any of the given constants"
    | some (goal, _) => return [goal]

elab "aesop_unfold " ids:ident+ " at " hyps:ident+ : tactic => do
  let toUnfold ← mkToUnfold ids
  liftMetaTactic λ goal => do
    let mut goal := goal
    for hypId in hyps do
      let fvarId := (← getLocalDeclFromUserName hypId.getId).fvarId
      match ← unfoldManyAt (toUnfold[·]?) goal fvarId with
      | none => throwTacticEx `aesop_unfold goal m!"could not unfold any of the given constants at hypothesis '{hypId}'"
      | some (goal', _) => goal := goal'
    return [goal]

end Aesop
