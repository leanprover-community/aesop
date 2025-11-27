/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import AesopPrecomp.RPINF
import Aesop.BaseM

open Lean

namespace Aesop

def rpinf (e : Expr) : BaseM RPINF :=
  profiling (fun stats _ elapsed => { stats with rpinf := stats.rpinf + elapsed } ) do
  rpinfCore e

end Aesop
