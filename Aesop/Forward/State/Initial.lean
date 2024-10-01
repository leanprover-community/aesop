/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.Index.Forward

open Lean Lean.Meta

namespace Aesop.ForwardIndex

def mkInitialForwardState (goal : MVarId) (idx : ForwardIndex) :
    MetaM ForwardState :=
  goal.withContext do
    let mut fs := ∅
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      let rules ← idx.get ldecl.type
      fs ← fs.addHyp goal ldecl.fvarId rules
    return fs


end Aesop.ForwardIndex
