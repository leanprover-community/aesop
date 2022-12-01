/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.RuleExpr
import Aesop.RuleSet

open Lean
open Lean.Elab

namespace Aesop.Frontend

namespace Parser

declare_syntax_cat Aesop.attr_rules

syntax Aesop.rule_expr : Aesop.attr_rules
syntax "[" Aesop.rule_expr,+,? "]" : Aesop.attr_rules

syntax (name := aesop) &"aesop" Aesop.attr_rules : attr

end Parser

structure AttrConfig where
  rules : Array RuleExpr
  deriving Inhabited

namespace AttrConfig

def «elab» (stx : Syntax) : TermElabM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| aesop $e:Aesop.rule_expr) => do
      let r ← RuleExpr.elab e |>.run ElabOptions.forAdditionalRules
      return { rules := #[r] }
    | `(attr| aesop [ $es:Aesop.rule_expr,* ]) => do
      let rs ← (es : Array Syntax).mapM λ e =>
        RuleExpr.elab e |>.run ElabOptions.forAdditionalRules
      return { rules := rs }
    | _ => throwUnsupportedSyntax

end AttrConfig


inductive AttributeEntry
  | rule (rsName : RuleSetName) (r : RuleSetMember)
  | ruleSet (rsName : RuleSetName)

initialize extension :
    PersistentEnvExtension AttributeEntry AttributeEntry Aesop.RuleSets ← do
  let ext ← registerPersistentEnvExtension {
    name := `aesop
    mkInitial := return {}
    addImportedFn := λ entriess => do
      let mut result := {}
      for entries in entriess do
        for entry in entries do
          match entry with
          | .rule rsName r => result := result.addRule rsName r
          | .ruleSet rsName => result := result.ensureRuleSet rsName
      return result
    addEntryFn := λ
      | rss, .rule rsName r => rss.addRule rsName r
      | rss, .ruleSet rsName => rss.ensureRuleSet rsName
    exportEntriesFn := λ rss => Id.run do
      let mut result := #[]
      for (rsName, _) in rss.others do
        result := result.push $ .ruleSet rsName
      for (rsName, r) in rss.globalRules do
        result := result.push $ .rule rsName r
      return result
  }
  let impl : AttributeImpl := {
    name := `aesop
    descr := "Register a declaration as an Aesop rule."
    applicationTime := .afterCompilation
    add := λ decl stx attrKind => withRef stx do
      match attrKind with
      | AttributeKind.global => pure ()
      | _ => throwError "local and scoped Aesop rules are not supported."
      let config ← runTermElabMAsCoreM $ AttrConfig.elab stx
      let rules ← runMetaMAsCoreM $
        config.rules.concatMapM (·.buildAdditionalGlobalRules decl)
      let mut rss := ext.getState (← getEnv)
      for (rule, rsNames) in rules do
        for rsName in rsNames do
          if ! rss.containsRuleSet rsName then throwError
            "no such rule set: '{rsName}'\n  (Use 'declare_aesop_rule_set' to declare rule sets.)"
          if rss.containsRule rsName rule.name then throwError
            "'{rule.name.name}' is already registered in rule set '{rsName}'."
          rss := rss.addRuleCore rsName rule
      setEnv $ ext.setState (← getEnv) rss
    erase := λ decl => do
      let rss := ext.getState (← getEnv)
      let rss ←
        rss.eraseRulesChecked
          { ruleSetNames := #[] }
          { ident := RuleIdent.const decl, builders := #[], phases := #[] }
      setEnv $ ext.setState (← getEnv) rss
  }
  -- Despite the name, this also works for non-builtin attributes.
  registerBuiltinAttribute impl
  return ext

variable [Monad m] [MonadEnv m]

def getAttributeRuleSets : m Aesop.RuleSets :=
  return extension.getState (← getEnv)

-- These rule sets are used when `aesop` is called without any options.
def getDefaultRuleSets (includeGlobalSimpTheorems := true) :
    CoreM Aesop.RuleSets := do
  let mut rss ← getAttributeRuleSets
  if includeGlobalSimpTheorems then
    let defaultSimpTheorems ← Meta.getSimpTheorems
    let defaultRs :=
      { rss.default with
        normSimpLemmas := defaultSimpTheorems.merge rss.default.normSimpLemmas }
    rss := { rss with default := defaultRs }
  return rss

def getDefaultRuleSet (includeGlobalSimpTheorems := true) :
    CoreM Aesop.RuleSet := do
  let rss ←
    getDefaultRuleSets (includeGlobalSimpTheorems := includeGlobalSimpTheorems)
  return rss.makeMergedRuleSet defaultEnabledRuleSets

def modifyAttributeRuleSets
    (f : Aesop.RuleSets → m Aesop.RuleSets) : m Unit := do
  let env ← getEnv
  let rss ← f $ extension.getState env
  setEnv $ extension.setState env rss

def isRuleSetDeclared (rsName : RuleSetName) : m Bool := do
  let rss ← getAttributeRuleSets
  return rss.containsRuleSet rsName

def declareRuleSet [MonadError m] (rsName : RuleSetName) : m Unit := do
  if rsName.isReserved then throwError
    "rule set name '{rsName}' is reserved"
  let rss ← getAttributeRuleSets
  if rss.containsRuleSet rsName then throwError
    "rule set '{rsName}' already declared"
  setEnv $ extension.setState (← getEnv) $ rss.addEmptyRuleSet rsName

end Aesop.Frontend
