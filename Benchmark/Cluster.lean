/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Basic

open Lean.Parser.Tactic (tacticSeq)

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

def testCluster  (nPremises : Nat) (nRules : Nat) (nClusters : Nat) (ts? : Option (TSyntax ``tacticSeq)) : CommandElabM Nanos := do
  let mut pNames := Array.mkEmpty nPremises
  let mut dArray : Array (Name × Nat) := Array.mkEmpty (nClusters * nPremises)
  /- The offset of the clusters -/
  let offset := 2
  let mut clusters : Array (Array Nat) := Array.mkEmpty nClusters
  for i in [:nClusters] do
    clusters := clusters.push (Array.ofFn (fun n : Fin nPremises ↦ (n : Nat) + i * (nPremises + offset)))
  for i in [:nClusters] do
    for j in [:nPremises] do
      pNames := pNames.push (Name.mkSimple $ "P" ++ toString i ++ toString j)
  /- Create an array with all the necessary data (Name of Premise and its `Nat`.) :
  #[(BM3P00,  0), (BM3P01,  1), (BM3P02,  2),
    (BM3P10,  5), (BM3P11,  6), (BM3P12,  7),
    (BM3P20, 10), (BM3P21, 11), (BM3P22, 12)] -/
  dArray := pNames.zip (clusters.flatten)

  for pNameN in dArray do
      elabCommand.go $ ← `(command| axiom $(mkIdent pNameN.1) : Nat → Nat → Prop)
  let binders : TSyntaxArray ``Term.bracketedBinder ←
    dArray.mapIdxM fun i pNameN ↦ do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
        $(mkIdent pNameN.1):ident $(Lean.Syntax.mkNatLit (pNameN.2))
          ($(Lean.Syntax.mkNatLit (pNameN.2 + 1)))))
  let sig : Term ← `(∀ $binders:bracketedBinder*, True)
  for i in [:nRules] do
    elabCommand.go $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  let binders : TSyntaxArray ``Term.bracketedBinder ←
     dArray.mapIdxM fun i pNameN ↦ do
      `(bracketedBinder| ($(mkIdent $ .mkSimple $ "p" ++ toString i) :
         $(mkIdent pNameN.1):ident $(Lean.Syntax.mkNatLit (pNameN.2))
          ($(Lean.Syntax.mkNatLit (pNameN.2 + 1)))))

  let ts ← ts?.getDM `(tacticSeq| time saturate; trivial)
  elabCommand.go $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t") $binders:bracketedBinder*
      : True := by $ts
  )
  timeRef.get

def cluster (nPremises nClusters : Nat) : Benchmark where
  title := s!"Cluster (variable number of rules, {nPremises} premises per rule, cluster size {nClusters})"
  fn nRules ts? := testCluster (nPremises := nPremises) (nClusters := nClusters) (nRules := nRules) ts?
