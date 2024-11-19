/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Aesop

set_option aesop.dev.statefulForward true

inductive SNat where
  | zero
  | succ (n : SNat)

def Nat.toSNat : Nat → SNat
  | zero => .zero
  | succ n => .succ n.toSNat

open Lean Lean.Meta Lean.Elab.Term in
elab "snat% " n:num : term => do
  let n ← elabTerm n (some $ .const ``Nat [])
  reduceAll (.app (.const ``Nat.toSNat []) n)

example (P : SNat → Prop) (h : P (snat% 50)) : True :=
  trivial

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser in
elab "test₁ " nPremises:num nLemmas:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nPs
  for i in [:nPs] do
    pNames := pNames.push (Name.mkSimple $ "P" ++ toString i)
  -- Create `axiom Pi : SNat → Prop` for i ∈ [0..nPs - 1]
  for pName in pNames do
    elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)
  -- Create `axiom Q : Prop`
  elabCommand $ ← `(command| axiom $(mkIdent `Q) : Prop)
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, $(mkIdent `Q) → True)
  -- Create `axiom li : ∀ n (p1 : P1 n) ... (pm : Pm n), Q → True` for
  -- i ∈ [0..nLemmas - 1] and m = nPs
  for i in [:nLemmas] do
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`
  -- where m = nPs.
  elabCommand $ ← `(command|
    theorem $(mkIdent `t₁) $binders:bracketedBinder* : True := by $ts
  )

/-
The tests from this file aim to compare best and worst cases of the two algorithms

Here are the tests
- Best case of the old
- Best case of the new
- Even fight (Rules are provable)
-/

test₁ 20 20 by
  -- set_option profiler true in
  -- set_option profiler.threshold 1 in
  -- set_option aesop.dev.statefulForward true in
  saturate
  trivial

/-
# nPremises = 100

nLemmas false true
 20      7     1070
 50      9     2600
 75      9     3920
100      9     5250
150     10     8270
200     10    11800

# nLemmas = 100

nPremises false true
 20        5      424
 50        7     1540
 75        7     3300
100        9     5230
150       12    10400
200       15    <fails>
-/
