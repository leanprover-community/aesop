/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Batteries.Tactic.SeqFocus

open Lean

namespace Aesop

def UnstructuredScriptBuilder (m : Type _ → Type _) := m (Array Syntax.Tactic)

instance [Pure m] : Inhabited (UnstructuredScriptBuilder m) :=
  ⟨pure #[]⟩

namespace UnstructuredScriptBuilder

variable [Monad m] [MonadQuotation m] [MonadError m]

@[inline]
def run (b : UnstructuredScriptBuilder m) : m (Array Syntax.Tactic) :=
  b

@[inline]
def ofTactics (ts : m (Array Syntax.Tactic)) : UnstructuredScriptBuilder m :=
  return (← ts)

@[inline]
def ofTactic (t : m Syntax.Tactic) : UnstructuredScriptBuilder m :=
  return #[← t]

@[inline]
def seq (b₁ b₂ : UnstructuredScriptBuilder m) : UnstructuredScriptBuilder m :=
  return (← b₁.run) ++ (← b₂.run)

@[inline]
def focusAndDoneEach (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  bs.mapM λ b => do `(tactic| { $(← b.run):tactic* })

@[inline]
def seqFocusAndDone (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) : UnstructuredScriptBuilder m :=
  b.seq (.focusAndDoneEach bs)

@[inline]
def seqFocus (b : UnstructuredScriptBuilder m)
    (bs : Array (UnstructuredScriptBuilder m)) :
    UnstructuredScriptBuilder m := do
  let ts ← b.run
  if bs.size == 0 then
    return ts
  let tss ← bs.mapM (·.run)
  if tss.all (·.isEmpty) then
    return ts
  if h : tss.size = 1 then
    let ts₂ := tss[0]'(by simp [h])
    return ts.push (← `(tactic| focus $ts₂:tactic*))
  else
    let tss ← tss.mapM λ (ts₂ : Array Syntax.Tactic) =>
      if ts₂.isEmpty then
        `(tactic| skip)
      else if h : ts₂.size = 1 then
        return ts₂[0]
      else
        `(tactic| ($ts₂:tactic*))
    if let some t := ts[ts.size - 1]? then
      return ts.pop.push (← `(tactic| $t:tactic <;> [ $tss;* ]))
    else
      return #[← `(tactic| map_tacs [ $tss;* ])]

@[inline]
protected def id : UnstructuredScriptBuilder m :=
  return #[]

end Aesop.UnstructuredScriptBuilder
