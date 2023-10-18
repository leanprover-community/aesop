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
import Aesop.BuiltinRules.Ext
import Aesop.BuiltinRules.Intros
import Aesop.BuiltinRules.Split
import Aesop.BuiltinRules.Subst
import Aesop.Frontend

namespace Aesop.BuiltinRules

attribute [aesop (rule_sets [builtin]) safe 0 apply] PUnit.unit

-- Hypotheses of product type are split by a separate builtin rule because the
-- `cases` builder currently cannot be used for norm rules.
attribute [aesop (rule_sets [builtin]) safe 101 constructors]
  And Prod PProd MProd

attribute [aesop (rule_sets [builtin]) unsafe 30% constructors]
  Exists Subtype Sigma PSigma

-- Sums are split and introduced lazily.
attribute [aesop (rule_sets [builtin]) [safe 100 cases, 50% constructors]]
  Or Sum PSum

-- A goal ⊢ P ↔ Q is split into ⊢ P → Q and ⊢ Q → P. Hypotheses of type `P ↔ Q`
-- are treated as equations `P = Q` by the simplifier and by our builtin subst
-- rule.
attribute [aesop (rule_sets [builtin]) safe 100 constructors] Iff

-- A negated goal Γ ⊢ ¬ P is transformed into Γ, P ⊢ ⊥. A goal with a
-- negated hypothesis Γ, h : ¬ P ⊢ Q is transformed into Γ[P := ⊥] ⊢ Q[P := ⊥]
-- by the simplifier. Quantified negated hypotheses h : ∀ x : T, ¬ P x are also
-- supported by the simplifier if the premises x can be discharged.
@[aesop (rule_sets [builtin]) safe 0]
theorem not_intro (h : P → False) : ¬ P := h

@[aesop (rule_sets [builtin]) norm destruct]
theorem empty_false (h : Empty) : False := nomatch h

@[aesop (rule_sets [builtin]) norm destruct]
theorem pEmpty_false (h : PEmpty) : False := nomatch h

attribute [aesop (rule_sets [builtin]) safe 0] Eq.refl HEq.refl

attribute [aesop (rule_sets [builtin]) norm constructors] ULift

attribute [aesop (rule_sets [builtin]) norm 0 destruct] ULift.down

@[aesop (rule_sets [builtin]) norm simp]
theorem heq_iff_eq (x y : α) : HEq x y ↔ x = y :=
  ⟨eq_of_heq, heq_of_eq⟩

end Aesop.BuiltinRules
