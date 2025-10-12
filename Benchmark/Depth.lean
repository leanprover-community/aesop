/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Basic

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "test " nPremises:num nQs:num nLemmas:num depth:num a:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nQs := nQs.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nLemmas := nLemmas.raw.isNatLit?
    | throwUnsupportedSyntax
  let some depth := depth.raw.isNatLit?
    | throwUnsupportedSyntax
  let some a := a.raw.isNatLit?
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
    pNames.mapIdxM λ i pName => do
      let mut n := a
      if i + 1= nPs - depth then n := a + 1
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
        $(mkIdent pName):ident (snat% $(Syntax.mkNatLit n))))
  -- Create `theorem t1 (p1 : P1 (snat% a)) ... (pm : Pm (snat% a)) : True := by ts`

  /- Inert hyps -/
  let bindersQ : TSyntaxArray ``Term.bracketedBinder ←
    --pNames.mapIdxM λ i pName => do
    (qNames).mapIdxM λ i qName => do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "q" ++ toString i) :
        $(mkIdent qName):ident (snat% $(Syntax.mkNatLit a))))
  -- Create `theorem t1 (p1 : P1 (snat% a)) ... (pm : Pm (snat% a)) : True := by ts`
  -- where m = nPs.
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $binders:bracketedBinder* $bindersQ:bracketedBinder*
      : True := by $ts
  )

/-
 **Uncomment for single test** :
test 6 0 100 1 0 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  saturate
  trivial

#check l1

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

In the stateful implementation, the lazy insertion optimisation, in combination
with the chosen slot ordering, leads to similar behaviour.

- `nPs` : Number of premises in the rules.
- `nQs` : Number of hypotheses in the context that do not unify with any premise
  of any rule.
- `nRs` : Number of rules; here they are all the same.
- `a` : Instantiation of the predicates in the rule.
  For larger values of `a`, premises and hypotheses take longer to unify.
- `d` : The depth: This is the number of slots considered before the procedure stops
   as the hypotheses are incompatible. This is well defined for `d ∈ [1,nPs]`.
-/
def benchDepth (nPs nQs nRs a : Nat) : Benchmark where
  title := s!"Depth (variable depth, {nPs} premises per rule, {nQs} additional hypotheses, {nRs} rules, term size {a})"
  fn := fun d => do
    let mut nPs := Syntax.mkNatLit nPs
    let mut nQs := Syntax.mkNatLit nQs
    let mut nRs := Syntax.mkNatLit nRs
    let mut d := Syntax.mkNatLit d
    let mut a := Syntax.mkNatLit a
    liftCoreM $ withoutModifyingState $ liftCommandElabM do
      elabCommand <| ← `(test $nPs $nQs $nRs $d $a by
        set_option maxRecDepth   1000000 in
        set_option maxHeartbeats 5000000 in
        time saturate
        trivial)
      timeRef.get
