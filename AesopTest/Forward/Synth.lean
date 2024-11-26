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
elab "test " nPremises:num nQs:num nLemmas:num erase:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nQs := nQs.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let some erase := erase.raw.isNatLit?
    | throwUnsupportedSyntax
  let nIter := erase
  let mut pNames := Array.mkEmpty nPs
  let mut qNames := Array.mkEmpty nQs
  for i in [:nPs] do
    pNames := pNames.push (Name.mkSimple $ "BM" ++ toString nIter ++ "P" ++ toString i)
  -- Create `axiom Pi : SNat → Prop` for i ∈ [0..nPs - 1]
  for pName in pNames do
    elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)

  for i in [:nQs] do
    qNames := qNames.push (Name.mkSimple $ "BM" ++ toString nIter ++ "Q" ++ toString i)
  -- Create `axiom Pi : SNat → Prop` for i ∈ [0..nPs - 1]
  for qName in qNames do
    elabCommand $ ← `(command| axiom $(mkIdent qName) : SNat → Prop)

  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, True)

  /- Rule that we are able to complete. -/
  let mut mNames := pNames
  let bindersM : TSyntaxArray ``Term.bracketedBinder ←
    (mNames.eraseIdx! erase).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sigM : Term ← `(∀ $(mkIdent `n) $bindersM:bracketedBinder*, True)
  elabCommand $ ← `(command|
      @[aesop safe]
      axiom $(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "lM"):ident : $sigM:term
    )


  --  ($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident $(mkIdent `n) $(mkIdent `n))
  -- Create `axiom li : ∀ n (p1 : P1 n) ... (pm : Pm n), Q → True` for
  -- i ∈ [0..nLemmas - 1] and m = nPs
  -- ($(mkIdent $ .mkSimple $ "q") :  $(mkIdent `Q):ident $(mkIdent `n))
  -- ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n))
  for i in [:nLemmas] do
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "l" ++ toString i):ident : $sig:term
    )

  /-
  Now we make the hyps for the context.
  -/
  /- Active hyps -/
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (mNames.eraseIdx! erase).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "p" ++ toString i) : $(mkIdent pName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`

  /- Inert hyps -/
  let bindersQ : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (qNames).mapIdxM λ i qName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "BM" ++ toString nIter ++ "q" ++ toString i) : $(mkIdent qName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`
  -- where m = nPs.
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "BM.t" ++ toString nIter) $binders:bracketedBinder* $bindersQ:bracketedBinder*
      --($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident (snat% 0) (snat% 0))
      : True := by $ts
  )

/-
Notes :
- The order of the old saturate is `n - 1, 0, 1, ..., n - 2`.
-/

/-
test 10 10 100 8 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward false in
  set_option trace.profiler true in
  saturate
  trivial
-/
