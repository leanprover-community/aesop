/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import Aesop
import AesopTest.Forward.Definitions
/-
Note :
- Having `2 ^ m` rules also means that we have `nPs * 2 ^ m` hyps since everything
is independent.
-/

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "testIndep " nPremises:num nRules:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nRules := nRules.raw.isNatLit?
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
      elabCommand $ ← `(command| axiom $(mkIdent pName) : Prop)

  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  let mut accBinders : TSyntaxArray ``Term.bracketedBinder := #[]

  for i in [:nRules] do
    binders : TSyntaxArray ``Term.bracketedBinder ←
      (pNamesArr[i]!).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident))
    let sig : Term ← `(∀ $binders:bracketedBinder*, $(mkIdent qNames[i]!):ident)
    accBinders := accBinders.append binders
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $accBinders:bracketedBinder*
      : True := by $ts
  )

/- **Uncomment for single test** :
testIndep 6 256 by
  set_option maxHeartbeats 5000000 in
  set_option aesop.dev.statefulForward true in
  set_option trace.profiler true in
  --set_option trace.aesop.forward true in
  --set_option trace.saturate true in
  --set_option profiler true in
  saturate
  trivial-/

def runTestIndep (nPs : Nat) (nRs : Nat) : CommandElabM Nanos := do
  let mut nPs := Syntax.mkNatLit nPs
  let mut nRs := Syntax.mkNatLit nRs
  let cmd := elabCommand <| ← `(testIndep $nPs $nRs by
    set_option maxHeartbeats 5000000 in
    set_option aesop.dev.statefulForward false in
    saturate
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd


/-
X : Old benchmark
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser in
elab "bmIndep " nPs:num nRules:num : command => do
  let some nRules:= nRules.raw.isNatLit?
    | throwUnsupportedSyntax
  for i in [:(nRules + 1)] do
    let mut inum := (Lean.Syntax.mkNatLit (2 ^ i))
    elabCommand $ ← `(command| testIndep $nPs $inum by
      set_option maxHeartbeats 5000000 in
      set_option aesop.dev.statefulForward true in
       set_option trace.profiler true in
      --set_option trace.aesop.forward true in
      --set_option trace.saturate true in
      --set_option profiler true in
      saturate
      trivial)
-/

/- n : number of premises --- m : means we test [1,2,..., 2 ^ m] rules -/
--bmIndep 6 8
