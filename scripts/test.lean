/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
open IO.Process
open System

/--
Aesop's test suite is just the `AesopTest` library.

When https://github.com/leanprover/lean4/pull/4142 is resolved we can remove this script.
-/
def main (_ : List String) : IO Unit := do
  let child ← IO.Process.spawn
    { cmd := "lake",
      args := #["build", "AesopTest"],
      env := #[("LEAN_ABORT_ON_PANIC", "1")] }
  exit (← child.wait).toUInt8
