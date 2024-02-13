/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.UnstructuredScriptBuilder

open Lean

namespace Aesop

structure StructuredScriptBuilder (m : Type → Type) where
  subgoals : Nat
  elim : Subarray (UnstructuredScriptBuilder m) → UnstructuredScriptBuilder m

instance [Pure m] : Inhabited (StructuredScriptBuilder m) :=
  ⟨{ subgoals := 0, elim := λ _ => default }⟩

namespace StructuredScriptBuilder

variable [Monad m] [MonadQuotation m] [MonadError m]

@[inline]
def run (b : StructuredScriptBuilder m) : m (Array Syntax.Tactic) :=
  b.elim #[].toSubarray

private def ensureContsSize (conts : Subarray α) (subgoals : Nat) :
    m (PLift (conts.size = subgoals)) := do
  if h : conts.size = subgoals then
    return ⟨h⟩
  else
    throwError "while building tactic syntax: tactic has {subgoals} subgoals but was given {conts.size} continuation tactics"

protected def id : StructuredScriptBuilder m where
  subgoals := 1
  elim conts := do
    let ⟨hconts⟩ ← ensureContsSize conts 1
    conts[0]'(by simp [hconts])

def ofTactics (subgoals : Nat) (ts : m (Array Syntax.Tactic)) :
    StructuredScriptBuilder m where
  subgoals := subgoals
  elim conts := do
    let ⟨hconts⟩ ← ensureContsSize conts subgoals
    if subgoals = 0 then
      UnstructuredScriptBuilder.ofTactics ts
    else if h : subgoals = 1 then
      UnstructuredScriptBuilder.ofTactics ts |>.seq (conts[0]'(by simp [*]))
    else
      UnstructuredScriptBuilder.ofTactics ts |>.seqFocusAndDone conts

@[inline]
def ofUnstructuredScriptBuilder (subgoals : Nat)
    (b : UnstructuredScriptBuilder m) : StructuredScriptBuilder m :=
  .ofTactics subgoals b

@[inline]
def ofTactic (subgoals : Nat) (t : m Syntax.Tactic) :
    StructuredScriptBuilder m :=
  .ofTactics subgoals (return #[← t])

@[inline]
def done : StructuredScriptBuilder m :=
  .ofTactics 0 (return #[])

def error (msg : MessageData) : StructuredScriptBuilder m where
  subgoals := 0
  elim _ := throwError "Unable to build tactic syntax: {msg}"

def seq (b : StructuredScriptBuilder m)
    (bs : Array (StructuredScriptBuilder m)) : StructuredScriptBuilder m :=
  let subgoals := bs.foldl (init := 0) λ n b => n + b.subgoals
  { subgoals
    elim := λ conts => do
      discard $ ensureContsSize bs.toSubarray b.subgoals
      discard $ ensureContsSize conts subgoals
      let mut bConts := Array.mkEmpty b.subgoals
      let mut start := 0
      for b' in bs do
        let «end» := start + b'.subgoals
        let b'Conts := conts[start:«end»]
        start := «end»
        bConts := bConts.push (b.elim b'Conts)
      b.elim bConts.toSubarray
  }

end Aesop.StructuredScriptBuilder
