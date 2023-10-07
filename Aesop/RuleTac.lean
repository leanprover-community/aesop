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
import Aesop.RuleTac.RuleApplicationWithMVarInfo
import Aesop.RuleTac.Tactic

open Lean

namespace Aesop.RuleTacDescr

protected def run : RuleTacDescr → RuleTacInput → MetaM RuleTacOutput
  | applyConst decl md => RuleTac.applyConst decl md
  | applyFVar userName md => RuleTac.applyFVar userName md
  | constructors cs md => RuleTac.applyConsts cs md
  | forwardConst decl    immediate clear md =>
    RuleTac.forwardConst decl immediate clear md
  | forwardFVar userName immediate clear md =>
    RuleTac.forwardFVar userName immediate clear md
  | cases decl md isRecursiveType => RuleTac.cases decl md isRecursiveType
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess

end RuleTacDescr
