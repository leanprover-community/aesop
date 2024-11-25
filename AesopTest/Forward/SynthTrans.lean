/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.dev.statefulForward true

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

inductive SNat where
  | zero
  | succ (n : SNat)

abbrev Nat.toSNat : Nat → SNat
  | zero => .zero
  | succ n => .succ n.toSNat

elab "snat% " n:num : term => do
  let n ← elabTerm n (some $ .const ``Nat [])
  reduceAll (.app (.const ``Nat.toSNat []) n)

elab "setup" : command => do
  let P := mkIdent `P
  elabCommand $ ← `(command| axiom $P : SNat → SNat → Prop)
  elabCommand $ ← `(command| @[aesop safe forward] axiom $(mkIdent `rule) : ∀ x y z, $P x y → $P y z → $P x z)

elab "test " nHyps:num firstNum:num " by " ts:tacticSeq : command => do
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

setup

set_option maxRecDepth   1000000 in
set_option maxHeartbeats 1000000 in
-- set_option profiler true in
test 10 300 by
  -- set_option trace.aesop.forward true in
  -- set_option trace.aesop.forward.debug true in
  saturate
  trivial
