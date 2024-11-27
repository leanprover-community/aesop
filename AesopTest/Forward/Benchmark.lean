/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import Aesop
import AesopTest.Forward.Synth
import AesopTest.Forward.SynthCascade
import AesopTest.Forward.SynthIndep
import AesopTest.Forward.SynthClusters

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

abbrev FuncType := Nat → CommandElabM Nanos

def withStatefulForward [MonadWithOptions m] (opt : Bool) (k : m α) : m α :=
  withOptions (fun opts ↦ aesop.dev.statefulForward.set opts opt) k

local instance : MonadWithOptions CommandElabM where
  withOptions f x := do
    let options := f (← getOptions)
    withScope (fun s ↦ {s with opts := options}) x

elab "bchmk " nIter:num " with " t:term " using " r:term : command => do
  let mut steps ← liftTermElabM do
    let t ← elabTerm t (some $ toTypeExpr (List Nat))
    unsafe Lean.Meta.evalExpr (List Nat) (toTypeExpr (List Nat)) t
  let nIter := nIter.getNat
  let func ← liftTermElabM do
    let r ← withSynthesize $ elabTerm r (some $ .const `FuncType [])
    unsafe Lean.Meta.evalExpr (Nat → CommandElabM Nanos) (.const `FuncType []) r
  for b in [true, false] do
    let mut ltimes : Array Nat := #[]
    for i in steps do
      let mut avr : Nat := 0
      for j in [:nIter] do
        avr := avr + (← withStatefulForward b $ func i).nanos
      ltimes := ltimes.push (avr / nIter)
    IO.println ("StatefulForward: " ++ toString b)
    IO.println <| (ltimes.map (·.toFloat / 1000000)).toList

def pows (n : Nat) : List Nat := (List.range n).map (2 ^ ·)
/- The old impl.'s premise order. -/
def steps (n : Nat) : List Nat := (n - 1) :: (List.range (n - 1)) ++ [n]

/-
**Uncomment to reveal parameters**
#check runTestErase
#check runTestIndep
#check runTestCascade
#check runTestCluster
-/

/-
**Uncomment to run tests**
local notation "k" => 10

bchmk 30 with steps k using fun n ↦ runTestErase k 0 k n
bchmk 30 with (pows 5) using fun n ↦ runTestIndep 6 n
bchmk 30 with (pows 5) using fun n ↦ runTestCascade n
bchmk 30 with (pows 6) using fun n ↦ runTestCluster n 3 (2 ^ 5 / n)
-/
