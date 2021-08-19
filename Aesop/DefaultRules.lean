/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.DefaultRules.Assumption
import Aesop.DefaultRules.ApplyHyps
import Aesop.DefaultRules.SplitHyps
import Aesop.Config

open Lean
open Lean.Elab
open Lean.Elab.Tactic

namespace Aesop.DefaultRules

-- TODO avoid TacticM?
def intros : TacticM Unit := do
  evalTactic (← `(tactic|intros))

def splitHyps : UserRuleTac := λ input =>
  return { regularGoals := #[(← splitAllHyps input.goal).snd] }

end DefaultRules

-- TODO As soon as the Aesop rule supports named rule sets, we can just
-- tag the above tactics with `@[aesop ... (rule_set default)]` or something.
def defaultRules : TermElabM (Array RuleSetMember) := do
  mkRules #[
    (``DefaultRules.assumption, ← `(attr|aesop safe -50)),
      -- The assumption rule is subsumed by applyHyps. But we still want to have
      -- it separately as a low-penalty safe rule so that very easy goals are
      -- discharged immediately.
    (``DefaultRules.intros    , ← `(attr|aesop norm -1)),
    (``DefaultRules.splitHyps , ← `(attr|aesop norm 0)),
    (``DefaultRules.applyHyps , ← `(attr|aesop 75%))]
  where
    mkRule (decl : Name) (configStx : Syntax) : TermElabM RuleSetMember := do
      let config ← RuleConfig.parse configStx
      config.applyToRuleIdent (RuleIdent.const decl)

    mkRules (rs : Array (Name × Syntax)) : TermElabM (Array RuleSetMember) :=
      rs.mapM (λ (decl, configStx) => mkRule decl configStx)

end Aesop
