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
attribute [aesop [norm 0 cases, safe 100 constructors]] And Prod PProd MProd
attribute [aesop [safe 0 cases, safe 100 constructors]] Exists Subtype Sigma
  PSigma
  -- TODO It should be possible to make the `cases` rule for Exists etc. a
  -- norm rule rather than a safe rule. However, this currently fails when the
  -- goal contains metavariables, since `cases` may replace the meta. Aesop
  -- then considers the replacement a newly introduced meta, which norm rules
  -- are not allowed to add.

-- Sums are split and introduced lazily.
attribute [aesop [safe 100 cases, 50% constructors]] Or Sum PSum

-- Iff is treated like a product.
attribute [aesop [norm 0 cases, safe 100 constructors]] Iff

attribute [aesop norm 0 [cases, constructors]] ULift

end Aesop.BuiltinRules
