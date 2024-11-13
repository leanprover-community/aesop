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
  elabCommand $ ← `(command| axiom $(mkIdent `A) : SNat → SNat → Prop)
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, True)
  --  ($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident $(mkIdent `n) $(mkIdent `n))
  -- Create `axiom li : ∀ n (p1 : P1 n) ... (pm : Pm n), Q → True` for
  -- i ∈ [0..nLemmas - 1] and m = nPs
  -- ($(mkIdent $ .mkSimple $ "q") :  $(mkIdent `Q):ident $(mkIdent `n))
  -- ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n))
  for i in [:nLemmas] do
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (pNames.filter (fun a ↦ false /-a != pNames[8]!-/)).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`
  -- where m = nPs.
  elabCommand $ ← `(command|
    theorem $(mkIdent `t₁) $binders:bracketedBinder*
      --($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident (snat% 0) (snat% 0))
      : True := by $ts
  )

/-
TODO :
I would like to know how to sequence tactics
Make a kind of graph.
In particular, I am worried that there are many cases in real life where
you have a shit ton of lemmas, a shit ton of hyps but nothing to add.
- Check at what point our method becomes totally unusable.
- Check for realistic cases :
  I would like many lemmas, two of them are completable
-/

/-
Notes :
- The order of the old saturate is `n - 1, 0, 1, ..., n - 2`.
- I think even though we don't add to a match, the fact is that we still store stuff
  or at least don't stop when `p0` is missing at the moment.
  Right we store the `hyps` in their corresponding slots.
- There exists a certain trade of, at some point, where it becomes worth to save the hyps.
  It would be nice to calculate this experiementaly.
-/

/-
Aim of this file :
-- Create `axiom li : ∀ n (q : Q n) (p1 : P1 n) ... (pm : Pm n) → True`

-/

test₁ 10 400 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial


#check l0
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
