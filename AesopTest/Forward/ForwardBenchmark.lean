/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import Aesop
import AesopTest.Forward.ForwardSynth

set_option aesop.dev.statefulForward true

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser in
elab "bm " nStep:num : command => do
  let some nStep := nStep.raw.isNatLit?
    | throwUnsupportedSyntax
  for i in [:nStep] do
    let inum := (Lean.Syntax.mkNatLit i)
    let nnum := (Lean.Syntax.mkNatLit (nStep))
    elabCommand $ ← `(test $nnum 10 100 $inum by
      set_option maxHeartbeats 5000000 in
      set_option aesop.dev.statefulForward true in
      -- set_option trace.profiler true in
      --set_option trace.aesop.forward true in
      --set_option trace.saturate true in
      --set_option profiler true in
      saturate
      trivial)

/-
Note :
- There is interference between each iteration, because we are always adding more rules.
-/

/-
Tests to do
-/

bm 10
