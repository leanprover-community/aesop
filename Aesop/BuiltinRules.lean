/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- The Aesop.BuiltinRules.* imports are needed to ensure that the tactics from
-- these files are registered.
import Aesop.BuiltinRules.Assumption
import Aesop.BuiltinRules.ApplyHyps
import Aesop.BuiltinRules.Reflexivity
import Aesop.Frontend

open Lean
open Lean.Elab
open Lean.Elab.Tactic

namespace Aesop.BuiltinRules

@[aesop norm -100 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def intros : TacticM Unit := do
  liftMetaTactic λ goal => do
    let (_, goal) ← Meta.intros goal
    return [goal]

@[aesop safe -30 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def contradiction : TacticM Unit :=
  liftMetaTactic λ goal => do Meta.contradiction goal; return []

-- Products are
-- - split eagerly, directly after norm simp, since these splits may enable
--   other rules to fire;
-- - introduced lazily since the introduction rules are somewhat expensive:
--   those for products split into multiple goals; those for existentials
--   introduce a metavariable. We want to wait as long as possible with either.
--   We could even consider making these rules `unsafe`.
attribute [aesop [safe -31 cases, safe 100 constructors]] And Prod PProd MProd
  Exists Sigma PSigma

end Aesop.BuiltinRules
