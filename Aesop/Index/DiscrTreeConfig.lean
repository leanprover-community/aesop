/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean.Meta

namespace Aesop

/-- Discrimination tree configuration used by all Aesop indices. -/
def discrTreeConfig : WhnfCoreConfig := { iota := false }

end Aesop
