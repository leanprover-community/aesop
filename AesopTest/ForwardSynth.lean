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
elab "test₁ " nPremises:num nLemmas:num "by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nPs
  for i in [:nPs] do
    pNames := pNames.push (Name.mkSimple $ "P" ++ toString i)
  for pName in pNames do
    elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)
  elabCommand $ ← `(command| axiom $(mkIdent `Q) : Prop)
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, $(mkIdent `Q) → True)
  for i in [:nLemmas] do
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident (snat% 0)))
  elabCommand $ ← `(command|
    theorem $(mkIdent `t₁) $binders:bracketedBinder* : True := by $ts
  )

test₁ 100 20 by
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
