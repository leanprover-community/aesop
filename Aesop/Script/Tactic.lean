/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean

namespace Aesop.Script

abbrev UTactic := Syntax.Tactic

abbrev STactic := Array Syntax.Tactic → Syntax.Tactic

structure Tactic where
  uTactic : UTactic
  sTactic? : Option STactic

namespace Tactic

instance : ToMessageData Tactic where
  toMessageData t := toMessageData t.uTactic

def unstructured (t : Syntax.Tactic) : Tactic where
  uTactic := t
  sTactic? := none

end Tactic

abbrev TacticBuilder := MetaM Tactic

end Aesop.Script
