/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Basic

/-
Note :
- Having `2 ^ m` rules also means that we have `nPs * 2 ^ m` hyps since everything
is independent.
-/

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "testIndep " nPremises:num nRules:num a:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nRules := nRules.raw.isNatLit?
    | throwUnsupportedSyntax
  let some a := a.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nPs
  let mut pNamesArr : Array (Array Name) := Array.mkEmpty nRules
  for i in [:nRules] do
    pNames := Array.mkEmpty nPs
    for j in [:nPs] do
      pNames := pNames.push (Name.mkSimple $ "P" ++ toString i ++ toString j)
    pNamesArr := pNamesArr.push pNames

  let mut qNames : Array Name := Array.mkEmpty nRules
  for i in [:nRules] do
    qNames := qNames.push (Name.mkSimple $ "Q" ++ toString i)

  for qName in qNames do
      elabCommand $ ← `(command| axiom $(mkIdent qName) : Prop)

  for pNames' in pNamesArr do
    for pName in pNames' do
      elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)

  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  let mut accBinders : TSyntaxArray ``Term.bracketedBinder := #[]

  for i in [:nRules] do
    binders : TSyntaxArray ``Term.bracketedBinder ←
      (pNamesArr[i]!).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident $(mkIdent `n)))
    let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, $(mkIdent qNames[i]!):ident)
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
    binders : TSyntaxArray ``Term.bracketedBinder ←
      (pNamesArr[i]!).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident (snat% $(Syntax.mkNatLit a))))
    accBinders := accBinders.append binders
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $accBinders:bracketedBinder*
      : True := by $ts
  )

/-
/- **Uncomment for single test** :-/
testIndep 6 10 0 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward false in
  set_option trace.profiler true in
  --set_option trace.aesop.forward true in
  --set_option trace.saturate true in
  --set_option profiler true in
  saturate
  trivial
-/

/--
#### Independent rules.

This benchmark compares the efficiency of the procedures on independent rules
and hypotheses.

Consider a set of predicates `P := {Pᵢⱼ ?n | 1 ≤ i ≤ nRs and 1 ≤ j ≤ nPs}` and
`Q := {Qᵢ | 1 ≤ i ≤ nRs}`.
We run the procedures with the `nRs` following rules
`rᵢ : ∀ n, Pᵢ₁ n → ... → Pᵢₙₚₛ n → Qᵢ`
and a context containing precisely `P`.

- `nPs` : Number of premises in the rules.
- `nRs` : Number of unique rules; they are independent but have the same number
  of premises.
- `a` : Instantiation of the predicates `Pᵢⱼ`.
  Note that `a` affects the run time as big numbers are harder to unify.
-/
def benchIndep (nPs a : Nat) : Benchmark where
  title := s!"Independence (variable number of rules, {nPs} premises per rule, term size {a})"
  fn := fun nRs => do
    let mut nPs := Syntax.mkNatLit nPs
    let mut nRs := Syntax.mkNatLit nRs
    let mut a := Syntax.mkNatLit a
    liftCoreM $ withoutModifyingState $ liftCommandElabM do
    elabCommand <| ← `(testIndep $nPs $nRs $a by
      set_option maxRecDepth   1000000 in
      set_option maxHeartbeats 5000000 in
      time saturate
      trivial)
    timeRef.get
