/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Rule

namespace Aesop

open Lean
open Lean.Meta
open Lean.Elab.Tactic (Tactic TacticM evalTactic)
open Lean.Elab.Term (evalExpr)

inductive RuleBuilderOutput (α : Type) : Type
| rule (r : Rule α) (imode : IndexingMode)
| simpLemmas (s : SimpLemmas)
  deriving Inhabited

def RuleBuilder α := DefinitionVal → TacticM (RuleBuilderOutput α)

namespace RuleBuilder

unsafe def tac : RuleBuilder α := λ c =>
  match c.type with
  -- TODO: is this correct?
  | `(tactic| $n) => do
    let t ← evalExpr (MVarId → MetaM (List MVarId)) c.name c.value
    pure $ RuleBuilderOutput.rule
      { tac := t,
        name := c.name,
        priorityInfo := sorry } -- How do we come up with this?
      IndexingMode.unindexed
  | _ => panic! "Expected {d.to_name} to have type `tactic`."

def applyIndexingMode (type : Expr) : TacticM IndexingMode := do
  let headConstant ← conclusionHeadConstant? type
  pure $
    match headConstant with
    | some c => indexTarget (toExpr c)
    | none => unindexed

def apply : RuleBuilder α := λ c => do
  let imode ← applyIndexingMode c.type
  let n := c.name
  pure $ RuleBuilderOutput.rule
    { tac := flip Meta.apply (mkConst n),
      name := "apply {n}",
      priorityInfo := sorry } -- TODO
    imode

def normalizationSimpLemma : RuleBuilder α := λ c => do
  let n := c.name
  let s ← SimpLemmas.empty.addConst n
    -- TODO: unsure how this fail! stuff works now
    -- <|> fail! "Expected {n} to be a (conditional) equation that can be used as a simp lemma."
  pure $ RuleBuilderOutput.simpLemmas s

unsafe def normalizationDefault : RuleBuilder α := λ c =>
  tac c <|> normalizationSimpLemma c
    -- TODO: unsure how this fail! stuff works now
    -- <|> fail! "Expected {c.to_name} to have type `tactic unit` or to be suitable as a simp lemma."

end RuleBuilder

end Aesop