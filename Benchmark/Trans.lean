/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Basic

open Aesop Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open Lean.Parser.Tactic (tacticSeq)

def testTrans (nHyps firstNum : Nat) (ts? : Option (TSyntax ``tacticSeq)) : CommandElabM Nanos := do
  let P := mkIdent `P
  elabCommand.go $ ← `(command| axiom $P : SNat → SNat → Prop)
  elabCommand.go $ ← `(command| @[aesop safe forward] axiom $(mkIdent `rule) : ∀ x y z, $P x y → $P y z → $P x z)
  let P := mkIdent `P
  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  for i in [:nHyps] do
    let mkNum n :=`(snat% $(Syntax.mkNatLit (firstNum + n)))
    let x₁ ← mkNum i
    let x₂ ← mkNum (i + 1)
    binders := binders.push $ ← `(bracketedBinder| (_ : $P $x₁ $x₂))
  let ts ← ts?.getDM `(tacticSeq| time saturate; trivial)
  elabCommand.go $ ← `(theorem foo $binders:bracketedBinder* : True := by $ts)
  timeRef.get

/--
#### Transitivity.

This test compares the efficiency of the procedures on a scaled-up version of
a transitivity problem.

Given some predicate `P ?x₁ ?x₂`, we register the rule `r : P x y → P y z → P x z`.
The procedures are then compared on a context containing `nHs` hypotheses
of the form `(h₁ : P a (n + 1)), ..., (hₙ : P (a + n - 1) (a + n))`.
Saturating this goal adds a total of `n(n-1)/2` hypotheses to the context.

`a` determines how long it takes to match hypotheses against premises.
-/
def trans (a : Nat) : Benchmark where
  title := s!"Transitivity (term size {a})"
  fn n ts? := testTrans (nHyps := n) (firstNum := a) ts?
