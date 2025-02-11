/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Aesop
import AesopTest.Forward.Definitions

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

--set_option aesop.dev.statefulForward true

elab "test " nPremises:num nQs:num nLemmas:num erase:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nQs := nQs.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let some erase := erase.raw.isNatLit?
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
    (pNames).mapIdxM λ i pName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
        $(mkIdent pName):ident $(mkIdent `n)))
  let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, True)

  /- Rule that we are able to complete. -/

  let mut mNames := pNames
  let bindersM : TSyntaxArray ``Term.bracketedBinder ←
    (mNames.eraseIdx! erase).mapIdxM λ i pName => do
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
    (mNames.eraseIdx! erase).mapIdxM λ i pName => do
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
    theorem $(mkIdent $ .mkSimple $ "t") $binders:bracketedBinder* $bindersQ:bracketedBinder*
      --($(mkIdent $ .mkSimple $ "a") : $(mkIdent `A):ident (snat% 0) (snat% 0))
      : True := by $ts
  )

/-
 **Uncomment for single test** :
test 6 0 100 1 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward false in
  set_option trace.profiler true in
  saturate
  trivial
-/

/--
#### Depth of considered rules.

This test compares the efficiency of the procedures in term of the depth
of the considered hypotheses.

In the stateless implementation, a rule `r` with `n` premises is selected
when a hypothesis matching its (last) slot `n` is present in the context.
The context's other hypotheses are then tried iteratively to fill the slots
`n-1`, `n-2`, etc.

The **depth** refers to the number of hypotheses sucessfully matched with the
premises of a rule until the rule is thrown out because it could not be completed.
For example, if a rule is not select, its depth is 0.
If we find hypotheses matching the slot `n` and `n-1` but not `n-2`, the depth is 2.

In the stateful implementation, this notion is mostly irrelevant as hypotheses
are saved regardless of their slot's position.

- `nPs` : Number of premises in the rules.
- `nQs` : Number of hypotheses in the context which do not unify with any premise
of any rule.
- `nRs` : Number of rules; here they are all the same.
- `e` : The number associated to the slot for which there is no hypothesis in
the context that match this slot.
If it is greater or equal to the number of premises, the context will contain
hypotheses matching all the slots and the rules will be applied.
-/
def runTestErase (nPs nQs nRs e : Nat) : CommandElabM Nanos := do
  let mut nPs := Syntax.mkNatLit nPs
  let mut nQs := Syntax.mkNatLit nQs
  let mut nRs := Syntax.mkNatLit nRs
  let mut e := Syntax.mkNatLit e
  let cmd := elabCommand <| ← `(test $nPs $nQs $nRs $e by
    set_option maxHeartbeats 5000000 in
    saturate
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd
