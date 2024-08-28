/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

namespace Aesop

open Lean Lean.Meta Lean.Parser.Tactic

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

private partial def addIdents (acc : Std.HashSet Name) : Syntax → Std.HashSet Name
  | .missing | .atom .. => acc
  | .ident (val := val) .. => acc.insert val
  | .node _ _ args =>
    args.foldl (init := acc) λ acc stx => addIdents acc stx

def optimizeInitialRenameI : Syntax → m Syntax
  | stx@`(tacticSeq| $tacs:tactic*) => do
    let tacs := tacs.getElems
    let some (tac : TSyntax `tactic) := tacs[0]?
      | return stx
    match tac with
    | `(tactic| rename_i $[$ns:ident]*) =>
      let usedNames := tacs[1:].foldl (init := ∅) λ usedNames stx =>
        addIdents usedNames stx.raw
      let mut dropUntil := 0
      for n in ns do
        if usedNames.contains n.getId then
          break
        else
          dropUntil := dropUntil + 1
      if dropUntil == 0 then
        return stx
      else if dropUntil == ns.size then
        tacsToTacticSeq tacs[1:]
      else
        let ns : TSyntaxArray `ident := ns[dropUntil:].toArray
        let tac ← `(tactic| rename_i $[$ns:ident]*)
        let mut result : Array (TSyntax `tactic) := Array.mkEmpty tacs.size
        result := result.push tac
        result := result ++ tacs[1:]
        tacsToTacticSeq result
    | _ => return stx
  | stx => return stx
where
  -- Inlining this helper function triggers a code gen issue:
  -- https://github.com/leanprover/lean4/issues/4548
  tacsToTacticSeq (tacs : Array (TSyntax `tactic)) : m (TSyntax ``tacticSeq) :=
    `(tacticSeq| $tacs:tactic*)

def optimizeSyntax (stx : TSyntax kind) : m (TSyntax kind) := do
  let mut stx := stx.raw
  stx ← optimizeFocusRenameI stx
  stx ← optimizeInitialRenameI stx
  return ⟨stx⟩

end Aesop
