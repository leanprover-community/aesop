/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Elab.Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

-- TODO This tactic simply executes the `MetaM` version of `cases`. We need this
-- when generating tactic scripts because the `MetaM` version and the `TacticM`
-- version of `cases` use different naming heuristics. If the two tactics were
-- harmonised, we could use regular `cases` in the script (assuming there are no
-- other differences).
elab &"aesop_cases" x:ident : tactic =>
  liftMetaTactic λ goal => do
    let fvarId ← getFVarFromUserName x.getId
    let subgoals ← goal.cases fvarId.fvarId!
    return subgoals.map (·.mvarId) |>.toList
