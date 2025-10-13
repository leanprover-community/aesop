/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Basic

open Lean.Parser.Tactic (tacticSeq)

set_option Elab.async false

/-
Note :
- Having `2 ^ m` rules also means that we have `nPs * 2 ^ m` hyps since everything
is independent.
-/

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

def testIndep (nPremises nRules a : Nat) (ts? : Option (TSyntax ``tacticSeq)) : CommandElabM Nanos := do
  let mut pNames := Array.mkEmpty nPremises
  let mut pNamesArr : Array (Array Name) := Array.mkEmpty nRules
  for i in [:nRules] do
    pNames := Array.mkEmpty nPremises
    for j in [:nPremises] do
      pNames := pNames.push (Name.mkSimple $ "P" ++ toString i ++ toString j)
    pNamesArr := pNamesArr.push pNames

  let mut qNames : Array Name := Array.mkEmpty nRules
  for i in [:nRules] do
    qNames := qNames.push (Name.mkSimple $ "Q" ++ toString i)

  for qName in qNames do
      elabCommand.go <| ← `(command| axiom $(mkIdent qName) : Prop)

  for pNames' in pNamesArr do
    for pName in pNames' do
      elabCommand.go <| ← `(command| axiom $(mkIdent pName) : SNat → Prop)

  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  let mut accBinders : TSyntaxArray ``Term.bracketedBinder := #[]

  for i in [:nRules] do
    binders : TSyntaxArray ``Term.bracketedBinder ←
      (pNamesArr[i]!).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident $(mkIdent `n)))
    let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, $(mkIdent qNames[i]!):ident)
    elabCommand.go <| ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
    binders : TSyntaxArray ``Term.bracketedBinder ←
      (pNamesArr[i]!).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident (snat% $(Syntax.mkNatLit a))))
    accBinders := accBinders.append binders

  let ts ← ts?.getDM do `(tacticSeq| time saturate; trivial)
  elabCommand.go <| ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $accBinders:bracketedBinder* : True := by $ts
  )
  timeRef.get

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
- `a` : Instantiation of the predicates `Pᵢⱼ`.
  Note that `a` affects the run time as big numbers are harder to unify.
- `nRs` : Number of unique rules; they are independent but have the same number
  of premises.
-/
def indep (nPs a : Nat) : Benchmark where
  title := s!"Independence (variable number of rules, {nPs} premises per rule, term size {a})"
  fn nRs ts? := testIndep (nPremises := nPs) (nRules := nRs) (a := a) ts?
