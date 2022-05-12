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
import Aesop.BuiltinRules.Intros
import Aesop.Frontend

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop.BuiltinRules

-- Product introduction is considered unsafe. This is to support situations like
--
--   def p := q ∧ r
--
-- where we may have a bunch of lemmas concluding `p`. If we then split `p` as
-- a safe rule, these lemmas never apply.
--
-- Hypotheses of product type are split by a separate builtin rule because the
-- `cases` builder currently cannot be used for norm rules.
attribute [aesop unsafe 30% constructors] And Prod PProd MProd
attribute [aesop unsafe 30% constructors] Exists Subtype Sigma
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

attribute [aesop norm 0 elim] ULift.down

end Aesop.BuiltinRules
