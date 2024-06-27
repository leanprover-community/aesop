/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Meta

namespace Aesop.SyntaxMap

inductive Key where
  | node (kind : SyntaxNodeKind)
  | atom (val : String)
  | ident (val : Name) -- TODO what about macro scopes in val?
  deriving Inhabited, BEq, Hashable

namespace Key

instance : ToString Key where
  toString
    | node kind => s!"node {kind}"
    | atom val => s!"atom {val}"
    | ident val => s!"ident {val}"

def ofSyntax : Syntax → Option Key
  | .missing => none
  | .node (kind := kind) .. => node kind
  | .atom (val := val) .. => atom val
  | .ident (val := val) .. => ident val.eraseMacroScopes

end SyntaxMap.Key

structure SyntaxMap (α : Type _) where
  toPHashMap : PHashMap SyntaxMap.Key α
  deriving Inhabited

structure SyntaxRewrite where
  keys : Array SyntaxMap.Key
  run : Syntax → CoreM (Option Syntax)
  deriving Inhabited

namespace SyntaxMap

protected def empty : SyntaxMap α :=
  ⟨.empty⟩

instance : EmptyCollection (SyntaxMap α) :=
  ⟨.empty⟩

def find? (key : Key) (m : SyntaxMap α) : Option α :=
  m.toPHashMap.find? key

def findStx? (stx : Syntax) (m : SyntaxMap α) : Option α := do
  let key ← Key.ofSyntax stx
  m.find? key

def insert (key : Key) (val : α) (m : SyntaxMap α) : SyntaxMap α :=
  ⟨m.toPHashMap.insert key val⟩

@[macro_inline]
def insertWith (key : Key) (a : α) (f : α → α) (m : SyntaxMap α) : SyntaxMap α :=
  match m.find? key with
  | some a' => m.insert key (f a')
  | none => m.insert key a

end SyntaxMap

abbrev SyntaxRewriteMap := SyntaxMap (List SyntaxRewrite)

namespace SyntaxRewriteMap

def insert (rw : SyntaxRewrite) (m : SyntaxRewriteMap) : SyntaxRewriteMap :=
  rw.keys.foldl (init := m) λ m key => m.insertWith key [rw] (rw :: ·)

end SyntaxRewriteMap

partial def optimizeSyntaxWith (rws : SyntaxRewriteMap) (stx : Syntax) :
    CoreM Syntax := do
  go stx
where
  go (stx : Syntax) : CoreM Syntax := withIncRecDepth do
    match stx with
    | .missing => return .missing
    | .node info kind args =>
      let args ← args.mapM go
      optimizeHead $ .node info kind args
    | .atom .. | .ident .. => optimizeHead stx

  optimizeHead (stx : Syntax) : CoreM Syntax := do
    let mut stx := stx
    while true do
      let some rws := rws.findStx? stx
        | return stx
      let some stx' ← rws.findSomeM? (·.run stx)
        | return stx
      stx := stx'
    return stx

def SyntaxRewrite.focusRenameI : SyntaxRewrite where
  keys :=
    let keyStxs := #[`(tactic| · simp), `(tactic| · { })] -- HACK
    keyStxs.map λ stx =>
      SyntaxMap.Key.ofSyntax (Unhygienic.run stx |>.raw) |>.get!
  run
    | `(tactic| · $tacs:tactic*)
    | `(tactic| · { $tacs:tactic* }) => do
      let tacs := tacs.getElems
      let some tac := tacs[0]?
        | return none
      match tac.raw with
      | `(tactic| rename_i $[$ns:ident]*) =>
        `(tactic| next $[$ns:ident]* => $(tacs[1:]):tactic*)
      | _ => return none
    | _ => return none

def optimizeSyntax (stx : TSyntax kind) : CoreM (TSyntax kind) :=
  let rws := #[SyntaxRewrite.focusRenameI]
  let rwMap := rws.foldl (init := ∅) (·.insert ·)
  return ⟨← optimizeSyntaxWith rwMap stx⟩

end Aesop
