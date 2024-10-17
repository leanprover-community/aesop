/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Extension
import Aesop.Frontend.RuleExpr

open Lean
open Lean.Elab

namespace Aesop.Frontend

namespace Parser

declare_syntax_cat Aesop.attr_rules

syntax Aesop.rule_expr : Aesop.attr_rules
syntax "[" Aesop.rule_expr,+,? "]" : Aesop.attr_rules

syntax (name := aesop) "aesop" Aesop.attr_rules : attr

end Parser

structure AttrConfig where
  rules : Array RuleExpr
  deriving Inhabited

namespace AttrConfig

def «elab» (stx : Syntax) : TermElabM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| aesop $e:Aesop.rule_expr) => do
      let r ← RuleExpr.elab e |>.run $ ← ElabM.Context.forAdditionalGlobalRules
      return { rules := #[r] }
    | `(attr| aesop [ $es:Aesop.rule_expr,* ]) => do
      let ctx ← ElabM.Context.forAdditionalGlobalRules
      let rs ← (es : Array Syntax).mapM λ e => RuleExpr.elab e |>.run ctx
      return { rules := rs }
    | _ => throwUnsupportedSyntax

end AttrConfig


initialize registerBuiltinAttribute {
  name := `aesop
  descr := "Register a declaration as an Aesop rule."
  applicationTime := .afterCompilation
  add := λ decl stx attrKind => withRef stx do
    let rules ← runTermElabMAsCoreM do
      let config ← AttrConfig.elab stx
      config.rules.flatMapM (·.buildAdditionalGlobalRules decl)
    for (rule, rsNames) in rules do
      for rsName in rsNames do
        addGlobalRule rsName rule attrKind (checkNotExists := true)
  erase := λ decl =>
    let ruleFilter :=
      { name := decl, scope := .global, builders := #[], phases := #[] }
    eraseGlobalRules RuleSetNameFilter.all ruleFilter (checkExists := true)
}

end Aesop.Frontend
