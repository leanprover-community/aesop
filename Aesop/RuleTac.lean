/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Apply
import Aesop.RuleTac.Basic
import Aesop.RuleTac.Cases
import Aesop.RuleTac.Forward
import Aesop.RuleTac.Preprocess
import Aesop.RuleTac.Tactic

open Lean

namespace Aesop.RuleTacDescr

protected def run : RuleTacDescr → RuleTac
  | apply t md => RuleTac.apply t md
  | constructors cs md => RuleTac.applyConsts cs md
  | forward t immediate clear => RuleTac.forward t immediate clear
  | cases target md isRecursiveType ctorNames =>
    RuleTac.cases target md isRecursiveType ctorNames
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacticStx stx => RuleTac.tacticStx stx
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess
  | forwardMatches m => RuleTac.forwardMatches m

end RuleTacDescr
