/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import Aesop
import Benchmark.Basic

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

def withStatefulForward [MonadWithOptions m] (opt : Bool) (k : m α) : m α :=
  withOptions (fun opts ↦ aesop.dev.statefulForward.set opts opt) k

local instance : MonadWithOptions CommandElabM where
  withOptions f x := do
    let options := f (← getOptions)
    withScope (fun s ↦ {s with opts := options}) x

/-
## The `bchmk` command.

This command runs a benchmark, both for the naive and incremental algorithm,
`nIter` times and outputs the average.

The term `t` should be a list of type `ℕ`.

The term `r` should be a `Benchmark`, which is executed `nIter` times for each
value in `t`.
-/
elab "bchmk " nIter:num " with " t:term " using " r:term : command => do
  let mut steps ← liftTermElabM do
    let t ← elabTerm t (some $ toTypeExpr (List Nat))
    unsafe Lean.Meta.evalExpr (List Nat) (toTypeExpr (List Nat)) t
  let nIter := nIter.getNat
  let benchmark ← liftTermElabM do
    let r ← withSynthesize $ elabTerm r (some $ .const ``Benchmark [])
    unsafe Lean.Meta.evalExpr Benchmark (.const ``Benchmark []) r
  IO.println benchmark.title
  for b in [false, true] do
    let mut ltimes : Array (Nat × Nat) := #[]
    for i in steps do
      let mut avr : Nat := 0
      for _ in [:nIter] do
        avr := avr + (← withStatefulForward b $ benchmark.fn i).nanos
      ltimes := ltimes.push ((i, avr / nIter))
    IO.println ("StatefulForward: " ++ toString b)
    for point in (ltimes.map (fun (i,n) ↦ (i, n.toFloat / 1000000))).toList do
      IO.print point
      IO.print " "
    IO.print "\n"

def pows (n : Nat) : List Nat := (List.range n).map (2 ^ ·)

def steps (n : Nat) : List Nat := (List.range' 1 (n - 1))
