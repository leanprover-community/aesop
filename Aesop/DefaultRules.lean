/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.DefaultRules.SplitHyps
import Aesop.Config

open Lean
open Lean.Elab
open Lean.Elab.Tactic

namespace Aesop.DefaultRules

def assumption : TacticM Unit :=
  liftMetaTactic λ goal => Lean.Meta.assumption goal *> pure []

def intros : TacticM Unit := do
  evalTactic (← `(tactic|intros))

def splitHyps : TacticM Unit :=
  liftMetaTactic λ goal => return [(← splitAllHyps goal).snd]

end DefaultRules

-- We could tag the above rule defs with the aesop attribute, and that would
-- certainly be more convenient than what this function does. However, the
-- attribute would come from the stage0 library, so any change to e.g.
-- the attribute syntax would require a stage0 update. These updates are a major
-- PITA when we rebase onto upstream master, so we want to minimise them.
def defaultRules : TermElabM (Array RuleSetMember) := do
  mkRules #[
    (``DefaultRules.assumption, ← `(attr|aesop safe 0)),
    (``DefaultRules.intros    , ← `(attr|aesop norm -1)),
    (``DefaultRules.splitHyps , ← `(attr|aesop norm 0)) ]
  where
    mkRule (decl : Name) (configStx : Syntax) : TermElabM RuleSetMember := do
      let config ← RuleConfig.parse configStx
      config.applyToRuleIdent (RuleIdent.const decl)

    mkRules (rs : Array (Name × Syntax)) : TermElabM (Array RuleSetMember) :=
      rs.mapM (λ (decl, configStx) => mkRule decl configStx)

end Aesop
