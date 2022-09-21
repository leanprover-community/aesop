/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop.RuleTac.Apply
import Aesop.RuleTac.Basic
import Aesop.RuleTac.Cases
import Aesop.RuleTac.Forward
import Aesop.RuleTac.RuleApplicationWithMVarInfo
import Aesop.RuleTac.Tactic

open Lean

namespace Aesop.RuleTacDescr

protected def run : RuleTacDescr → RuleTacInput → MetaM RuleTacOutput
  | applyConst decl => RuleTac.applyConst decl
  | applyFVar userName => RuleTac.applyFVar userName
  | constructors cs => RuleTac.applyConsts cs
  | forwardConst decl    immediate clear =>
    RuleTac.forwardConst decl immediate clear
  | forwardFVar userName immediate clear =>
    RuleTac.forwardFVar userName immediate clear
  | cases decl isRecursiveType => RuleTac.cases decl isRecursiveType
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl

end RuleTacDescr
