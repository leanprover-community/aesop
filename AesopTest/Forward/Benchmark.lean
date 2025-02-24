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
import AesopTest.Forward.SynthTrans

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

abbrev FuncType := Nat → CommandElabM Nanos

def withStatefulForward [MonadWithOptions m] (opt : Bool) (k : m α) : m α :=
  withOptions (fun opts ↦ aesop.dev.statefulForward.set opts opt) k

local instance : MonadWithOptions CommandElabM where
  withOptions f x := do
    let options := f (← getOptions)
    withScope (fun s ↦ {s with opts := options}) x

/-
## The `bchmk` command.

For a given test, that runs the `saturate` tactic in some given context,
this command runs the test, both for the naive and incremental algorithm
`nIter` times and outputs the average.

The term `t` should be a list of type `ℕ`.

The term `r` expects a function `ℕ → Aesop.Nanos`.
Most tests used in this projects take multiple `ℕ` argument with
the intended use to fix all of them but one.
The function `ℕ → Aesop.Nanos` is then instantiated for each value of `t`.
-/
elab "bchmk " nIter:num " with " t:term " using " r:term : command => do
  let mut steps ← liftTermElabM do
    let t ← elabTerm t (some $ toTypeExpr (List Nat))
    unsafe Lean.Meta.evalExpr (List Nat) (toTypeExpr (List Nat)) t
  let nIter := nIter.getNat
  let func ← liftTermElabM do
    let r ← withSynthesize $ elabTerm r (some $ .const `FuncType [])
    unsafe Lean.Meta.evalExpr (Nat → CommandElabM Nanos) (.const `FuncType []) r
  IO.println ((r.raw[1][3][0].getId).toString ++ " with unification challenge "
     ++ (r.raw[1][3][1][r.raw[1][3][1].getNumArgs - 1].toNat.repr))
  for b in [false, true] do
    let mut ltimes : Array (Nat × Nat) := #[]
    for i in steps do
      let mut avr : Nat := 0
      for j in [:nIter] do
        avr := avr + (← withStatefulForward b $ func i).nanos
      ltimes := ltimes.push ((i, avr / nIter))
    IO.println ("StatefulForward: " ++ toString b)
    for point in (ltimes.map (fun (i,n) ↦ (i, n.toFloat / 1000000))).toList do
      IO.print point
      IO.print " "
    IO.println ("")

def pows (n : Nat) : List Nat := (List.range n).map (2 ^ ·)
def steps (n : Nat) : List Nat := (List.range' 1 (n - 1))
