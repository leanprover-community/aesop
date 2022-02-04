/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

namespace Aesop

open Lean

-- All times are in milliseconds.
structure ProfilingTimes where
  configParsing : Nat
  ruleSetConstruction : Nat
  search : Nat
  deriving Inhabited

namespace ProfilingTimes

open MessageData in
instance : ToMessageData ProfilingTimes where
  toMessageData t :=
    "execution times (all in ms):" ++ node #[
      m!"configuration parsing: {t.configParsing}",
      m!"rule set construction: {t.ruleSetConstruction}",
      m!"search: {t.search}"
    ]

end Aesop.ProfilingTimes
