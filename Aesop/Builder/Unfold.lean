/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleBuilder

def unfold : RuleBuilder :=
  ofGlobalRuleBuilder .unfold λ _ decl =>
    return .unfold { decl, unfoldThm? := ← getUnfoldEqnFor? decl }

end Aesop.RuleBuilder
