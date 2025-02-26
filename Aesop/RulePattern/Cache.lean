/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.Substitution
import Aesop.Rule.Name

open Lean

set_option linter.missingDocs true

namespace Aesop

/-- Entry of the rule pattern cache. -/
def RulePatternCache.Entry := Array (RuleName × Substitution)

set_option linter.missingDocs false in
/-- A cache for the rule pattern index. -/
structure RulePatternCache where
  map : Std.HashMap Expr RulePatternCache.Entry
  deriving Inhabited

instance : EmptyCollection RulePatternCache :=
  ⟨⟨∅⟩⟩

end Aesop
