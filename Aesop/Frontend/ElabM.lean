/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean
open Lean.Elab

namespace Aesop.Frontend

structure ElabOptions where
  parsePriorities : Bool
  parseBuilderOptions : Bool

namespace ElabOptions

def forAdditionalRules : ElabOptions where
  parsePriorities := true
  parseBuilderOptions := true

def forErasing : ElabOptions where
  parsePriorities := false
  parseBuilderOptions := false

end ElabOptions


abbrev ElabM := ReaderT ElabOptions TermElabM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad ElabM :=
  { inferInstanceAs (Monad ElabM) with }

end Aesop.Frontend
