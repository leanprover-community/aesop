/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleSet

open Lean

namespace Aesop

/--
An environment extension containing an Aesop rule set. Each rule set has its
own extension.
-/
abbrev RuleSetExtension := SimpleScopedEnvExtension RuleSetMember RuleSet

initialize aesopExtensionsMapRef : IO.Ref (HashMap Name RuleSetExtension) ←
  IO.mkRef ∅

end Aesop
