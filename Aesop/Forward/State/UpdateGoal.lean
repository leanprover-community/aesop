/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State
import Aesop.Tree.TreeM
import Aesop.Tree.RunMetaM

open Lean

namespace Aesop.GoalRef

def updateForwardState (phase : PhaseName) (gref : GoalRef) : TreeM Unit := do
  let g ← gref.get
  if phase == .norm then
    throwError "aesop: internal error: {decl_name%}: at goal {g.id}: norm phase not supported"
  if ! g.isNormal then
    throwError "aesop: internal error: {decl_name%}: attempt to update forward state of non-normal goal {g.id} to phase {phase}"
  let (fs, ms) ← g.runMetaMInPostNormState' fun goal =>
    g.forwardState.update goal phase
  let ms := g.forwardRuleMatches.update ms ∅ ∅
  gref.set <| g.setForwardState fs |>.setForwardRuleMatches ms

end Aesop.GoalRef
