/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Meta

variable [Monad m] [MonadQuotation m]

partial def optimizeFocusRenameI : Syntax → m Syntax
  | stx@.missing | stx@(.atom ..) | stx@(.ident ..) => return stx
  | .node info kind args => do
    let stx := .node info kind (← args.mapM optimizeFocusRenameI)
    match stx with
    | `(tactic| · $tacs:tactic*)
    | `(tactic| · { $tacs:tactic* }) => do
      let tacs := tacs.getElems
      let some (tac : TSyntax `tactic) := tacs[0]?
        | return stx
      match tac with
      | `(tactic| rename_i $[$ns:ident]*) =>
        `(tactic| next $[$ns:ident]* => $(tacs[1:]):tactic*)
      | _ => return stx
    | _ => return stx

def optimizeSyntax (stx : TSyntax kind) : m (TSyntax kind) :=
  return ⟨← optimizeFocusRenameI stx.raw⟩

end Aesop
