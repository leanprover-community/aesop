/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule.Name
import Aesop.RPINF.Basic

set_option linter.missingDocs true

open Lean

namespace Aesop

/-- Instantiations for the variables occurring in a `RulePattern`. -/
def RulePatternInstantiation := Array Expr
  deriving Inhabited, BEq, Hashable, ToMessageData

/-- Instantiations for the variables occurring in a `RulePattern`. All
instantiations are in RPINF. -/
def RPINFRulePatternInstantiation := Array RPINF
  deriving Inhabited, BEq, Hashable, ToMessageData

namespace RulePatternInstantiation

/-- View a `RulePatternInstantiation` as an array of expressions. -/
def toArray : RulePatternInstantiation → Array Expr :=
  id

instance : EmptyCollection RulePatternInstantiation :=
  ⟨.empty⟩

end RulePatternInstantiation

namespace RPINFRulePatternInstantiation

/-- View an `RPINFRulePatternInstantiation` as an array of expressions in
RPINF. -/
def toArray : RPINFRulePatternInstantiation → Array RPINF :=
  id

/-- View an `RPINFRulePatternInstantiation` as a `RulePatternInstantiation`. -/
def toRulePatternInstantiation (inst : RPINFRulePatternInstantiation) :
    RulePatternInstantiation :=
  inst.map (·.toExpr)

instance : EmptyCollection RPINFRulePatternInstantiation :=
  ⟨.empty⟩

end RPINFRulePatternInstantiation

/-- Entry of the rule pattern cache. -/
def RulePatternCache.Entry := Array (RuleName × RulePatternInstantiation)

set_option linter.missingDocs false in
/-- A cache for the rule pattern index. -/
structure RulePatternCache where
  map : Std.HashMap Expr RulePatternCache.Entry
  deriving Inhabited

instance : EmptyCollection RulePatternCache :=
  ⟨⟨∅⟩⟩

end Aesop
