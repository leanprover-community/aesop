/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

namespace Aesop.BuiltinRules

open Lean Lean.Meta

@[aesop 80% tactic (index := [target _ = _]) (rule_sets := [builtin])]
def ext : RuleTac := RuleTac.ofSingleRuleTac λ input => do
  let (goals, steps) ← unhygienicExtS input.goal |>.run
  return (goals, steps, none)

end Aesop.BuiltinRules
