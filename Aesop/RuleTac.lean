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

protected def run : RuleTacDescr → RuleTacInput → MetaM RuleTacOutput
  | applyConst decl md pat? => RuleTac.applyConst decl pat? md
  | applyTerm stx md pat? => RuleTac.applyTerm stx pat? md
  | constructors cs md => RuleTac.applyConsts cs md
  | forwardConst decl pat? immediate clear md =>
    RuleTac.forwardConst decl pat? immediate clear md
  | forwardTerm stx pat? immediate clear md =>
    RuleTac.forwardTerm stx pat? immediate clear md
  | cases decl md isRecursiveType => RuleTac.cases decl md isRecursiveType
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacticStx stx => RuleTac.tacticStx stx
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess

end RuleTacDescr
