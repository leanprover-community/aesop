/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
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


def runTestTrans (nHs : Nat) (fH : Nat) : CommandElabM Nanos := do
  let mut nHs := Syntax.mkNatLit nHs
  let mut fH := Syntax.mkNatLit fH
  let cmd := elabCommand <| ← `(testTrans $nHs $fH by
    set_option maxRecDepth   1000000 in
    set_option maxHeartbeats 5000000 in
    saturate [*]
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd
