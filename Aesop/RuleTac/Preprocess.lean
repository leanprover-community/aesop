/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean Lean.Meta

namespace Aesop.RuleTac

/--
This `RuleTac` is applied once to the root goal, before any other rules are
tried.
-/
def preprocess : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (postMVarId, _, scriptBuilder?) ←
    renameInaccessibleFVarsWithScript input.goal input.options.generateScript
  return (#[postMVarId], scriptBuilder?, none)

end Aesop.RuleTac
