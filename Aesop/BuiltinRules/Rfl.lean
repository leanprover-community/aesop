/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

open Lean Lean.Elab.Tactic

namespace Aesop.BuiltinRules

@[aesop safe 0 (rule_sets := [builtin])]
def rfl : RuleTac :=
  RuleTac.ofTacticSyntax λ _ => `(tactic| rfl)

end Aesop.BuiltinRules
