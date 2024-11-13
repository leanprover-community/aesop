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
elab "test₁ " nPremises:num nQs:num nLemmas:num remStart:num remStop:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nQs := nQs.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let some remStart := remStart.raw.isNatLit?
    | throwUnsupportedSyntax
  let some remStop := remStop.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nPs
  let mut qNames := Array.mkEmpty nQs
  for i in [:nPs] do
    pNames := pNames.push (Name.mkSimple $ "P" ++ toString i)
  -- Create `axiom Pi : SNat → Prop` for i ∈ [0..nPs - 1]
  for pName in pNames do
    elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)

  for i in [:nQs] do
    qNames := qNames.push (Name.mkSimple $ "Q" ++ toString i)
  -- Create `axiom Pi : SNat → Prop` for i ∈ [0..nPs - 1]
  for qName in qNames do
    elabCommand $ ← `(command| axiom $(mkIdent qName) : SNat → Prop)

  let binders : TSyntaxArray ``Term.bracketedBinder ←
    pNames.mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, True)

  /- Rule that we are able to complete. -/
  let mut mNames' := pNames.zipWithIndex
  mNames' := mNames'.filter (fun ⟨name, i⟩ => if i < remStart ∨ remStop < i then true else false)
  let mNames := mNames'.unzip.1
  let bindersM : TSyntaxArray ``Term.bracketedBinder ←
    (mNames).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident $(mkIdent `n)))
  let sigM : Term ← `(∀ $(mkIdent `n) $bindersM:bracketedBinder*, True)
  elabCommand $ ← `(command|
      @[aesop safe]
      axiom $(mkIdent $ .mkSimple $ "lM"):ident : $sigM:term
    )


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

  /-
  Now we make the hyps for the context.
  -/
  /- Active hyps -/
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (mNames).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) : $(mkIdent pName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`

  /- Inert hyps -/
  let bindersQ : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (qNames).mapIdxM λ i qName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "q" ++ toString i) : $(mkIdent qName):ident (snat% 0)))
  -- Create `theorem t1 (p1 : P1 (snat% 0)) ... (pm : Pm (snat% 0)) : True := by ts`
  -- where m = nPs.
  elabCommand $ ← `(command|
    theorem $(mkIdent `t₁) $binders:bracketedBinder* $bindersQ:bracketedBinder*
      --($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident (snat% 0) (snat% 0))
      : True := by $ts
  )

/-
Notes :
- The order of the old saturate is `n - 1, 0, 1, ..., n - 2`.
-/

/-
Basic test for **Inactive premises**
We always have `1` active premises and `5 * 2 ^ n` inactives ones.

-/

namespace t0
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 6 0 100 0 4 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t0

namespace t1
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 11 0 100 0 9 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t1

namespace t2
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 21 0 100 0 19 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t2

namespace t3
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 41 0 100 0 39 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t3

namespace t4
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 81 0 100 0 79 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t4

namespace t5
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 161 0 100 0 159 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t5

namespace t6
/-
Meaning of options (`rem` is for remove):
`nPs` `nQs` `nLemmas` `remStart` `remStop` -/
test₁ 321 0 100 0 319 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l0
#check lM

end t6
