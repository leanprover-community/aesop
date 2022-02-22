/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean

namespace Aesop.Frontend

structure ParseOptions where
  parsePriorities : Bool
  parseBuilderOptions : Bool

namespace ParseOptions

def forAdditionalRules : ParseOptions where
  parsePriorities := true
  parseBuilderOptions := true

def forErasing : ParseOptions where
  parsePriorities := false
  parseBuilderOptions := false

end ParseOptions


abbrev ParseT := ReaderT ParseOptions

instance [AddErrorMessageContext m] : AddErrorMessageContext (ParseT m) where
  add stx msg := AddErrorMessageContext.add (m := m) stx msg

end Aesop.Frontend
