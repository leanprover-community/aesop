/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Aesop
import AesopTest.Forward.Definitions

open Aesop Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "testTrans " nHyps:num firstNum:num " by " ts:tacticSeq : command => do
  let P := mkIdent `P
  elabCommand $ ← `(command| axiom $P : SNat → SNat → Prop)
  elabCommand $ ← `(command| @[aesop safe forward] axiom $(mkIdent `rule) : ∀ x y z, $P x y → $P y z → $P x z)
  let some nHyps := nHyps.raw.isNatLit?
    | throwUnsupportedSyntax
  let some firstNum := firstNum.raw.isNatLit?
    | throwUnsupportedSyntax
  let P := mkIdent `P
  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  for i in [:nHyps] do
    let mkNum n :=
      if i % 2 == 0 then
        `(Nat.toSNat $(Syntax.mkNatLit (firstNum + n)))
      else
        `(snat% $(Syntax.mkNatLit (firstNum + n)))
    let x₁ ← mkNum i
    let x₂ ← mkNum (i + 1)
    binders := binders.push $ ← `(bracketedBinder| (_ : $P $x₁ $x₂))
  elabCommand $ ← `(theorem foo $binders:bracketedBinder* : True := by $ts)

-- set_option trace.profiler true in
-- testTrans 5 300 by
--   set_option maxHeartbeats 5000000 in
--   set_option maxRecDepth   1000000 in
--   --set_option maxHeartbeats 1000000 in
--   set_option aesop.dev.statefulForward false in
--   saturate
--   trivial

/--
#### Transitivity.

This test compares the efficiency of the procedures on scaled up version of
a transitivity problem.

Given some predicate `P ?x₁ ?x₂`, we register the rule `r : P x y → P y z → P x z`.
The procedures are then compared on a context containing `nHs` hypotheses
of the form `(h₁ : P a (n + 1)), ..., (hₙ : P (a + n - 1) (a + n))`.
Saturating this goal adds a total of `n(n-1)/2` hypotheses to the context.

- `nHs` : Number of hypotheses in the context.
- `a` : Starting integer for the transitivity chain.
Note that this affects the run time as big number are designed to be much
harder to unify.
-/
def runTestTrans (n : Nat) (a : Nat) : CommandElabM Nanos := do
  let mut nHs := Syntax.mkNatLit n
  let mut fH := Syntax.mkNatLit a
  let cmd := elabCommand <| ← `(testTrans $nHs $fH by
    set_option maxRecDepth   1000000 in
    set_option maxHeartbeats 5000000 in
    saturate [*]
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd
