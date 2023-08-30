/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/

import Aesop.Search.Expansion.Simp.Basic

open Lean
open Lean.Meta
open Lean.Meta.Simp (UsedSimps)

namespace Aesop

def simpAll (mvarId : MVarId) (ctx : Simp.Context)
    (usedSimps : UsedSimps := {}) : MetaM SimpResult := do
  let ctx := { ctx with config.failIfUnchanged := false }
  match ← Lean.Meta.simpAll mvarId ctx usedSimps with
  | (none, usedSimps) => return .solved usedSimps
  | (some mvarIdNew, usedSimps) =>
    if mvarIdNew == mvarId then
      return .unchanged mvarIdNew
    else
      return .simplified mvarIdNew usedSimps

end Aesop
