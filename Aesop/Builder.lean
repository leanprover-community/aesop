/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Apply
import Aesop.Builder.Basic
import Aesop.Builder.Cases
import Aesop.Builder.Constructors
import Aesop.Builder.Default
import Aesop.Builder.Forward
import Aesop.Builder.NormSimp
import Aesop.Builder.Tactic

open Lean

namespace Aesop.GlobalRuleTacBuilderDescr

def toRuleTacBuilder : GlobalRuleTacBuilderDescr → GlobalRuleTacBuilder
  | apply decl => GlobalRuleTacBuilder.apply decl
  | constructors cs => GlobalRuleTacBuilder.constructors cs
  | forward decl immediate clear => GlobalRuleTacBuilder.forwardCore decl immediate clear
  | cases decl isRecursiveType => GlobalRuleTacBuilder.cases decl isRecursiveType
  | tacticM decl => GlobalRuleTacBuilder.tacticM decl
  | simpleRuleTac decl => GlobalRuleTacBuilder.simpleRuleTac decl
  | ruleTac decl => GlobalRuleTacBuilder.ruleTac decl

end GlobalRuleTacBuilderDescr


namespace Rule'

@[inline]
def descrToTac (goal : MVarId) (r : Rule' α GlobalRuleTacBuilderDescr) :
    MetaM (Rule' α RuleTacWithBuilderDescr) :=
  r.mapTacM (·.toRuleTacBuilder)

end Aesop.Rule'
