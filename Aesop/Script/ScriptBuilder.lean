/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.StructuredScriptBuilder
import Aesop.Util.Tactic

open Lean
open Lean.Meta
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop

structure ScriptBuilder (m) where
  unstructured : UnstructuredScriptBuilder m
  structured : StructuredScriptBuilder m

instance [Pure m] : Inhabited (ScriptBuilder m) :=
  ⟨default, default⟩

namespace ScriptBuilder

variable [Monad m] [MonadQuotation m] [MonadError m]

protected def id : ScriptBuilder m where
  unstructured := .id
  structured := .id

def ofTactics (subgoals : Nat) (ts : m (Array Syntax.Tactic)) :
    ScriptBuilder m where
  unstructured := .ofTactics ts
  structured := .ofTactics subgoals ts

@[inline]
def ofUnstructuredScriptBuilder (subgoals : Nat)
    (b : UnstructuredScriptBuilder m) : ScriptBuilder m :=
  .ofTactics subgoals b

def ofTactic (subgoals : Nat) (t : m Syntax.Tactic) : ScriptBuilder m where
  unstructured := .ofTactic t
  structured := .ofTactic subgoals t

def seq (b : ScriptBuilder m) (bs : Array (ScriptBuilder m)) :
    ScriptBuilder m where
  unstructured := b.unstructured.seqFocus $ bs.map (·.unstructured)
  structured := b.structured.seq $ bs.map (·.structured)

@[inline, always_inline]
def withPrefix (f : TSyntax ``tacticSeq → m (Array (TSyntax `tactic)))
    (b : ScriptBuilder m) : ScriptBuilder m where
  unstructured := do
    let ts ← b.unstructured
    f (← `(tacticSeq| $ts:tactic*))
  structured := {
    subgoals := b.structured.subgoals
    elim := λ ks => do
      let ts ← b.structured.elim ks
      f (← `(tacticSeq| $ts:tactic*))
  }

protected def withTransparency (md : TransparencyMode) (b : ScriptBuilder m) :
    ScriptBuilder m :=
  b.withPrefix λ ts =>
    return #[← `(tactic| ($(← withTransparencySeqSyntax md ts)))]

protected def withAllTransparency (md : TransparencyMode) (b : ScriptBuilder m) :
    ScriptBuilder m :=
  b.withPrefix λ ts =>
    return #[← `(tactic| ($(← withAllTransparencySeqSyntax md ts)))]

end ScriptBuilder

abbrev RuleTacScriptBuilder := ScriptBuilder MetaM

@[inline, always_inline]
def mkScriptBuilder? (generateScript : Bool)
    (builder : ScriptBuilder MetaM) : Option (ScriptBuilder MetaM) :=
  if generateScript then
    some builder
  else
    none

end Aesop
