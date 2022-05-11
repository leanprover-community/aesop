/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- The Aesop.BuiltinRules.* imports are needed to ensure that the tactics from
-- these files are registered.
import Aesop.BuiltinRules.Assumption
import Aesop.BuiltinRules.ApplyHyps
import Aesop.BuiltinRules.DestructProducts
import Aesop.Frontend

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop.BuiltinRules

@[aesop norm -100 (tactic (uses_branch_state := false)) (rule_sets [builtin])]
def intros : RuleTac := λ input => do
    let (newFVars, goal) ← Meta.intros input.goal
    if newFVars.size == 0 then
      throwError "nothing to introduce"
    let postState ← saveState
    let mvars ← getGoalMVarsNoDelayed goal
    return {
      applications := #[{
        goals := #[(goal, mvars)]
        postState
        introducedMVars := {}
        assignedMVars := {}
      }]
      postBranchState? := none
    }

-- Products are introduced lazily since the introduction rules are somewhat
-- expensive: those for products split into multiple goals; those for
-- existentials introduce a metavariable. We want to wait as long as possible
-- with either. We could even consider making these rules `unsafe`.
--
-- Hypotheses of product type are split by a separate builtin rule because the
-- `cases` builder currently cannot be used for norm rules.
attribute [aesop safe 100 constructors] And Prod PProd MProd
attribute [aesop safe 100 constructors] Exists Subtype Sigma
  PSigma

-- Sums are split and introduced lazily.
attribute [aesop [safe 100 cases, 50% constructors]] Or Sum PSum

-- Iff is treated as a product.
attribute [aesop safe 100 constructors] Iff

@[aesop [norm 0 elim]]
theorem Iff_elim (h : α ↔ β) : (α → β) ∧ (β → α) :=
  ⟨h.mp, h.mpr⟩

attribute [aesop safe 0] Eq.refl HEq.refl

attribute [aesop norm constructors] ULift

attribute [aesop [norm 0 elim]] ULift.down

end Aesop.BuiltinRules
