/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Elab Lean.Elab.Term

namespace Aesop.Frontend.Parser

declare_syntax_cat Aesop.bool_lit (behavior := symbol)

syntax "true" : Aesop.bool_lit
syntax "false" : Aesop.bool_lit

end Parser

def elabBoolLit [Monad m] [MonadRef m] [MonadExceptOf Exception m]
    (stx : TSyntax `Aesop.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => throwUnsupportedSyntax

end Aesop.Frontend
