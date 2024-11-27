/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Aesop
import AesopTest.Forward.Definitions

/-
Note :
- This test is done with `Nat` as it is hard to create distinct clusters over `SNat`
  with approximately the same size a one big cluster.
- The total number of premises is the number of premises per cluster * number of cluster.
  Thus, it makes senses to tests out different ratios.
  E.g.
  For 64 premises we can tests out :
  - 1 cluster with 64 premises
  - 2 clusters with 32 premises
  - ...
  - 64 clusters with 1 premise
-/

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "testCluster " nPremises:num nRules:num nClusters:num " by " ts:tacticSeq : command => do
  let some nPs := nPremises.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nRules := nRules.raw.isNatLit?
    | throwUnsupportedSyntax
  let some nClusters := nClusters.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nPs
  let mut dArray : Array (Name × Nat) := Array.mkEmpty (nClusters * nPs)
  /- The offset of the clusters -/
  let offset := 2
  let mut clusters : Array (Array Nat) := Array.mkEmpty nClusters
  for i in [:nClusters] do
    clusters := clusters.push (Array.ofFn (fun n : Fin nPs ↦ (n : Nat) + i * (nPs + offset)))
  for i in [:nClusters] do
    for j in [:nPs] do
      pNames := pNames.push (Name.mkSimple $ "P" ++ toString i ++ toString j)
  /- Create an array with all the necessary data (Name of Premise and its `Nat`.) :
  #[(BM3P00,  0), (BM3P01,  1), (BM3P02,  2),
    (BM3P10,  5), (BM3P11,  6), (BM3P12,  7),
    (BM3P20, 10), (BM3P21, 11), (BM3P22, 12)] -/
  dArray := pNames.zip (clusters.flatten)

  for pNameN in dArray do
      elabCommand $ ← `(command| axiom $(mkIdent pNameN.1) : Nat → Nat → Prop)
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    dArray.mapIdxM fun i pNameN ↦ do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
        $(mkIdent pNameN.1):ident $(Lean.Syntax.mkNatLit (pNameN.2))
          ($(Lean.Syntax.mkNatLit (pNameN.2 + 1)))))
  let sig : Term ← `(∀ $binders:bracketedBinder*, True)
  for i in [:nRules] do
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  let binders : TSyntaxArray ``Term.bracketedBinder ←
     dArray.mapIdxM fun i pNameN ↦ do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
         $(mkIdent pNameN.1):ident $(Lean.Syntax.mkNatLit (pNameN.2))
          ($(Lean.Syntax.mkNatLit (pNameN.2 + 1)))))
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $binders:bracketedBinder*
      : True := by $ts
  )

def runTestCluster (nPs : Nat) (nRs : Nat) (nCs : Nat) : CommandElabM Nanos := do
  let mut nPs := Syntax.mkNatLit nPs
  let mut nRs := Syntax.mkNatLit nRs
  let mut nCs := Syntax.mkNatLit nCs
  let cmd := elabCommand <| ← `(testCluster $nPs $nRs $nCs by
    set_option maxHeartbeats 5000000 in
    set_option aesop.dev.statefulForward false in
    saturate
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd


--X : Old benchmark; These don't seems to exactly match the new? TODO: Investigate.
/-
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser in
elab "bmClusters " nTPs:num nRules:num : command => do
  let some nTPs := nTPs.raw.isNatLit?
    | throwUnsupportedSyntax
  for i in [:(nTPs + 1)] do
    let mut inum := (Lean.Syntax.mkNatLit (2 ^ i))
    let mut inuminv := (Lean.Syntax.mkNatLit ((2 ^ nTPs) / (2 ^ i)))
    elabCommand $ ← `(testCluster $inum $nRules $inuminv by
      set_option maxHeartbeats 5000000 in
      set_option aesop.dev.statefulForward false in
      set_option trace.profiler true in
      --set_option trace.aesop.forward true in
      --set_option trace.saturate true in
      --set_option profiler true in
      saturate
      trivial)

/- log of the total number of hyps - number of rules -/
bmClusters 7 3
-/
