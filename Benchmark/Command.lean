/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import Aesop
import Benchmark.Basic

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open Lean.Parser.Tactic (tacticSeq)

/-
## The `bchmk` command.

This command runs a benchmark, both for the naive and incremental algorithm,
`nIter` times and outputs the average.

The term `l` should be a list of type `ℕ`.

The term `b` should be a `Benchmark`, which is executed `nIter` times for each
value in `l`.

See `Benchmark/Basic` for the definition of the `Benchmark` type.
-/
elab "bchmk " nIter:num " with " l:term " using " b:term ts?:(" by " tacticSeq)? : command => do
  let ts? : Option (TSyntax ``tacticSeq) := ts?.map (⟨·.raw⟩)
  let steps ← liftTermElabM do
    let l ← elabTerm l (some $ toTypeExpr (List Nat))
    unsafe Lean.Meta.evalExpr (List Nat) (toTypeExpr (List Nat)) l
  let nIter := nIter.getNat
  let benchmark ← liftTermElabM do
    let b ← withSynthesize $ elabTerm b (some $ .const ``Benchmark [])
    unsafe Lean.Meta.evalExpr Benchmark (.const ``Benchmark []) b
  IO.println benchmark.title
  for b in [false, true] do
    let mut ltimes : Array (Nat × Nat) := #[]
    for i in steps do
      let mut avr : Nat := 0
      for _ in [:nIter] do
        avr := avr + (← benchmark.run i ts? (statefulForward := b)).nanos
      ltimes := ltimes.push ((i, avr / nIter))
    IO.println ("StatefulForward: " ++ toString b)
    for point in (ltimes.map (fun (i,n) ↦ (i, n.toFloat / 1000000))).toList do
      IO.print point
      IO.print " "
    IO.print "\n"

def pows (n : Nat) : List Nat := (List.range n).map (2 ^ ·)

def steps (n : Nat) : List Nat := (List.range' 1 (n - 1))
