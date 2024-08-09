/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Extension.Init

open Lean Lean.Meta

namespace Aesop.Frontend

def extensionDescr (rsName : RuleSetName) :
    SimpleScopedEnvExtension.Descr BaseRuleSetMember BaseRuleSet where
  name := rsName
  addEntry rs r := rs.add r
  initial := ∅

def declareRuleSetUnchecked (rsName : RuleSetName) (isDefault : Bool) :
    IO Unit := do
  let ext ← registerSimpleScopedEnvExtension $ extensionDescr rsName
  let simpExtName := .mkStr1 s!"aesop_{rsName}"
  discard $ registerSimpAttr simpExtName (ref := simpExtName)
    s!"simp theorems in the Aesop rule set '{rsName}'"
  let simprocExtName := .mkStr1 s!"aesop_{rsName}_proc"
  discard $ Simp.registerSimprocAttr simprocExtName (name := simprocExtName)
    (ref? := none) s!"simprocs in the Aesop rule set '{rsName}'"
  declaredRuleSetsRef.modify λ rs =>
    let ruleSets := rs.ruleSets.insert rsName (ext, simpExtName, simprocExtName)
    let defaultRuleSets :=
      if isDefault then
        rs.defaultRuleSets.insert rsName
      else
        rs.defaultRuleSets
    { ruleSets, defaultRuleSets }

def isRuleSetDeclared (rsName : RuleSetName) : IO Bool :=
  return (← getDeclaredRuleSets).contains rsName

variable [Monad m] [MonadError m] [MonadLiftT IO m]
  [MonadLiftT (ST IO.RealWorld) m] [MonadEnv m] [MonadResolveName m]

def checkRuleSetNotDeclared (rsName : RuleSetName) : m Unit := do
  if ← isRuleSetDeclared rsName then
    throwError "rule set '{rsName}' already exists"

def declareRuleSet (rsName : RuleSetName) (isDefault : Bool) : m Unit := do
  checkRuleSetNotDeclared rsName
  declareRuleSetUnchecked rsName isDefault

initialize
  builtinRuleSetNames.forM (declareRuleSetUnchecked (isDefault := true))

def getGlobalRuleSetData (rsName : RuleSetName) :
    m (RuleSetExtension × Name × SimpExtension × Name × Simp.SimprocExtension) := do
  let (some (ext, simpExtName, simprocExtName)) :=
    (← getDeclaredRuleSets)[rsName]?
    | throwError "no such rule set: '{rsName}'\n  (Use 'declare_aesop_rule_set' to declare rule sets.\n   Declared rule sets are not visible in the current file; they only become visible once you import the declaring file.)"
  let some simpExt ← getSimpExtension? simpExtName
    | throwError "internal error: expected '{simpExtName}' to be a declared simp extension"
  let some simprocExt ← Simp.getSimprocExtension? simpExtName
    | throwError "internal error: expected '{simpExtName}' to be a declared simp extension"
  return (ext, simpExtName, simpExt, simprocExtName, simprocExt)

def getGlobalRuleSetFromData (ext : RuleSetExtension) (simpExt : SimpExtension)
    (simprocExt : Simp.SimprocExtension) : m GlobalRuleSet := do
  let env ← getEnv
  let base := ext.getState env
  let simpTheorems := simpExt.getState env
  let simprocs := simprocExt.getState env
  return { base with simpTheorems, simprocs }

def getGlobalRuleSet (rsName : RuleSetName) :
    CoreM (GlobalRuleSet × Name × Name) := do
  let (ext, simpExtName, simpExt, simprocExtName, simprocExt) ←
    getGlobalRuleSetData rsName
  let rs ← getGlobalRuleSetFromData ext simpExt simprocExt
  return (rs , simpExtName, simprocExtName)

def getGlobalRuleSets (rsNames : Array RuleSetName) :
    CoreM (Array (GlobalRuleSet × Name × Name)) :=
  rsNames.mapM getGlobalRuleSet

def getDefaultGlobalRuleSets : CoreM (Array (GlobalRuleSet × Name × Name)) := do
  getGlobalRuleSets (← getDefaultRuleSetNames).toArray

def getDeclaredGlobalRuleSets :
    CoreM (Array (RuleSetName × GlobalRuleSet × Name × Name)) := do
  (← getDeclaredRuleSets).toArray.mapM λ (rsName, _) =>
    return (rsName, ← getGlobalRuleSet rsName)

def modifyGetGlobalRuleSet (rsName : RuleSetName)
    (f : GlobalRuleSet → α × GlobalRuleSet) : m α := do
  let (ext, _, simpExt, _, simprocExt) ← getGlobalRuleSetData rsName
  let env ← getEnv
  let base := ext.getState env
  let simpTheorems := simpExt.getState env
  let simprocs := simprocExt.getState env
  let env := ext.modifyState env λ _ => default     -- an attempt to preserve linearity
  let env := simpExt.modifyState env λ _ => default -- ditto
  let env := simprocExt.modifyState env λ _ => default -- ditto
  let rs := { base with simpTheorems, simprocs }
  let (a, rs) := f rs
  let env := ext.modifyState env λ _ => rs.toBaseRuleSet
  let env := simpExt.modifyState env λ _ => rs.simpTheorems
  setEnv env
  return a

def modifyGlobalRuleSet (rsName : RuleSetName)
    (f : GlobalRuleSet → GlobalRuleSet) : CoreM Unit := do
  modifyGetGlobalRuleSet rsName λ rs => ((), f rs)

def addGlobalRule (rsName : RuleSetName) (r : GlobalRuleSetMember)
    (kind : AttributeKind) (checkNotExists : Bool) : m Unit := do
  let (ext, _, simpExt, _, simprocExt) ← getGlobalRuleSetData rsName
  if checkNotExists then
    let rs ← getGlobalRuleSetFromData ext simpExt simprocExt
    if rs.contains r.name then
      throwError "aesop: rule '{r.name.name}' is already registered in rule set '{rsName}'"
  match r with
  | .base m => ext.add m kind
  | .normSimpRule r => do
    for e in r.entries do
      simpExt.add e kind
      -- Workaround for a Lean bug.
      if let .thm l := e then
        setEnv $ simpExt.modifyState (← getEnv) λ simpTheorems =>
          { simpTheorems with erased := simpTheorems.erased.erase l.origin }

def eraseGlobalRules (rsf : RuleSetNameFilter) (rf : RuleFilter)
    (checkExists : Bool) : m Unit := do
  match rsf.matchedRuleSetNames with
  | none =>
    let anyErased ←
      (← getDeclaredRuleSets).foldM (init := false) λ b rsName _ => go b rsName
    if checkExists && ! anyErased then
      throwError "'{rf.name}' is not registered (with the given features) in any rule set."
  | some rsNames =>
    let anyErased ← rsNames.foldlM (init := false) go
    if checkExists && ! anyErased then
      throwError "'{rf.name}' is not registered (with the given features) in any of the rule sets {rsNames.map toString}."
  where
    go (anyErased : Bool) (rsName : RuleSetName) : m Bool :=
      modifyGetGlobalRuleSet rsName λ rs =>
        let (rs, anyErasedFromRs) := rs.erase rf
        (anyErased || anyErasedFromRs, rs)

end Aesop.Frontend
