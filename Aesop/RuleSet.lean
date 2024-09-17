/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Index
import Aesop.RuleSet.Filter
import Aesop.RuleSet.Member

open Lean Lean.Meta

namespace Aesop

section Types

set_option linter.missingDocs true

/--
The Aesop-specific parts of an Aesop rule set. A `BaseRuleSet` stores global
Aesop rules, e.g. safe and unsafe rules. It does not store simp theorems for
the builtin norm simp rule; these are instead stored in a simp extension.
-/
structure BaseRuleSet where
  /--
  Normalisation rules registered in this rule set.
  -/
  normRules : Index NormRuleInfo
  /--
  Unsafe rules registered in this rule set.
  -/
  unsafeRules : Index UnsafeRuleInfo
  /--
  Safe rules registered in this rule set.
  -/
  safeRules : Index SafeRuleInfo
  /--
  Rules for the builtin unfold rule. A pair `(decl, unfoldThm?)` in this map
  represents a declaration `decl` which should be unfolded. `unfoldThm?` should
  be the output of `getUnfoldEqnFor? decl` and is cached here for efficiency.
  -/
  unfoldRules : PHashMap Name (Option Name)
  /--
  The set of rules that were erased from `normRules`, `unsafeRules` and
  `safeRules`. When we erase a rule which is present in any of these three
  indices, the rule is not removed from the indices but just added to this set.
  By contrast, when we erase a rule from `unfoldRules`, we actually delete it.
  -/
  erased : PHashSet RuleName
  /--
  A cache of the names of all rules registered in this rule set. Invariant:
  `ruleNames` contains exactly the names of the rules present in `normRules`,
  `unsafeRules`, `safeRules` and `unfoldRules` and not present in `erased`. We
  use this cache (a) to quickly determine whether a rule is present in the rule
  set and (b) to find the full rule names associated with the fvar or const
  identified by a name.
  -/
  ruleNames : PHashMap Name (UnorderedArraySet RuleName)
  deriving Inhabited

/--
A global Aesop rule set. When we tag a declaration with `@[aesop]`, it is stored
in one or more of these rule sets. Internally, a `GlobalRuleSet` is composed of
a `BaseRuleSet` (stored in an Aesop rule set extension) plus a set of simp
theorems (stored in a `SimpExtension`).
-/
structure GlobalRuleSet extends BaseRuleSet where
  /--
  The simp theorems stored in this rule set.
  -/
  simpTheorems : SimpTheorems
  /--
  The simprocs stored in this rule set.
  -/
  simprocs : Simprocs
  deriving Inhabited

/--
The rule set used by an Aesop tactic call. A local rule set is produced by
combining several global rule sets and possibly adding or erasing some
individual rules.
-/
structure LocalRuleSet extends BaseRuleSet where
  /--
  The simp theorems used by the builtin norm simp rule.
  -/
  simpTheoremsArray : Array (Name × SimpTheorems)
  /--
  The simp theorems array must contain at least one `SimpTheorems` structure.
  When a simp theorem is added to a `LocalRuleSet`, it is stored in this first
  `SimpTheorems` structure.
  -/
  simpTheoremsArrayNonempty : 0 < simpTheoremsArray.size
  /--
  The simprocs used by the builtin norm simp rule.
  -/
  simprocsArray : Array (Name × Simprocs)
  /--
  The simprocs array must contain at least one `Simprocs` structure, for the
  same reason as above.
  -/
  simprocsArrayNonempty : 0 < simprocsArray.size
  /--
  FVars that were explicitly added as simp rules.
  -/
  localNormSimpRules : Array LocalNormSimpRule

end Types


namespace GlobalRuleSet

@[inline, always_inline]
def onBaseM [Monad m] (f : BaseRuleSet → m (BaseRuleSet × α))
    (rs : GlobalRuleSet) : m (GlobalRuleSet × α) := do
  let (toBaseRuleSet, a) ← f rs.toBaseRuleSet
  let rs := { rs with toBaseRuleSet }
  return (rs, a)

@[inline, always_inline]
def onBase (f : BaseRuleSet → BaseRuleSet × α) (rs : GlobalRuleSet) :
    GlobalRuleSet × α :=
  rs.onBaseM (m := Id) f

@[inline, always_inline]
def modifyBaseM [Monad m] (f : BaseRuleSet → m BaseRuleSet)
    (rs : GlobalRuleSet) : m GlobalRuleSet :=
  (·.fst) <$> rs.onBaseM (λ rs => return (← f rs, ()))

@[inline, always_inline]
def modifyBase (f : BaseRuleSet → BaseRuleSet) (rs : GlobalRuleSet) :
    GlobalRuleSet :=
  rs.modifyBaseM (m := Id) f

end GlobalRuleSet


namespace LocalRuleSet

@[inline, always_inline]
def onBaseM [Monad m] (f : BaseRuleSet → m (BaseRuleSet × α))
    (rs : LocalRuleSet) : m (LocalRuleSet × α) := do
  let (toBaseRuleSet, a) ← f rs.toBaseRuleSet
  return ({ rs with toBaseRuleSet }, a)

@[inline, always_inline]
def onBase (f : BaseRuleSet → (BaseRuleSet × α)) (rs : LocalRuleSet) :
    LocalRuleSet × α :=
  rs.onBaseM (m := Id) f

def modifyBaseM [Monad m] (f : BaseRuleSet → m BaseRuleSet) (rs : LocalRuleSet) :
    m LocalRuleSet :=
  (·.fst) <$> rs.onBaseM (λ rs => return (← f rs, ()))

def modifyBase (f : BaseRuleSet → BaseRuleSet) (rs : LocalRuleSet) :
    LocalRuleSet :=
  rs.modifyBaseM (m := Id) f

end LocalRuleSet


def BaseRuleSet.trace (rs : BaseRuleSet) (traceOpt : TraceOption) :
    CoreM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  withConstAesopTraceNode traceOpt (return "Erased rules") do
    aesop_trace![traceOpt] "(Note: even if these rules appear in the sections below, they will not be applied by Aesop.)"
    let erased := rs.erased.fold (init := #[])
      λ ary r => ary.push r
    for r in erased.qsortOrd do
      aesop_trace![traceOpt] r
  withConstAesopTraceNode traceOpt (return "Unsafe rules") do
    rs.unsafeRules.trace traceOpt
  withConstAesopTraceNode traceOpt (return "Safe rules") do
    rs.safeRules.trace traceOpt
  withConstAesopTraceNode traceOpt (return "Normalisation rules") do
    rs.normRules.trace traceOpt
  withConstAesopTraceNode traceOpt (return "Constants to unfold") do
    for r in rs.unfoldRules.toArray.map (·.fst.toString) |>.qsortOrd do
      aesop_trace![traceOpt] r

def GlobalRuleSet.trace (rs : GlobalRuleSet) (traceOpt : TraceOption) :
    CoreM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  rs.toBaseRuleSet.trace traceOpt
  withConstAesopTraceNode traceOpt (return "Normalisation simp theorems:") do
    traceSimpTheorems rs.simpTheorems traceOpt
  -- TODO trace simprocs

def LocalRuleSet.trace (rs : LocalRuleSet) (traceOpt : TraceOption) :
    CoreM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  rs.toBaseRuleSet.trace traceOpt
  withConstAesopTraceNode traceOpt (return "Simp sets used by normalisation simp:") do
    rs.simpTheoremsArray.map (printSimpSetName ·.fst) |>.qsortOrd.forM λ s => do
      aesop_trace![traceOpt] s
  withConstAesopTraceNode traceOpt (return "Local normalisation simp theorems") do
    for r in rs.localNormSimpRules.map (·.simpTheorem) do
      aesop_trace![traceOpt] r
where
  printSimpSetName : Name → String
    | `_ => "<default>"
    | n => toString n


def BaseRuleSet.empty : BaseRuleSet where
  normRules := ∅
  unsafeRules := ∅
  safeRules := ∅
  unfoldRules := {}
  ruleNames := {}
  erased := ∅

instance : EmptyCollection BaseRuleSet :=
  ⟨.empty⟩

def GlobalRuleSet.empty : GlobalRuleSet where
  toBaseRuleSet := ∅
  simpTheorems := {}
  simprocs := {}

instance : EmptyCollection GlobalRuleSet :=
  ⟨.empty⟩

def LocalRuleSet.empty : LocalRuleSet where
  toBaseRuleSet := .empty
  simpTheoremsArray := #[(`_, {})]
  simpTheoremsArrayNonempty := by decide
  simprocsArray := #[(`_, {})]
  simprocsArrayNonempty := by decide
  localNormSimpRules := ∅

instance : EmptyCollection LocalRuleSet :=
  ⟨.empty⟩

instance : Inhabited LocalRuleSet :=
  ⟨∅⟩


private def BaseRuleSet.isErased (rs : BaseRuleSet) (n : RuleName) : Bool :=
  rs.erased.contains n

def BaseRuleSet.contains (rs : BaseRuleSet) (n : RuleName) : Bool :=
  ! rs.isErased n &&
  if let some ns := rs.ruleNames.find? n.name then
    ns.contains n
  else
    false

def GlobalRuleSet.contains (rs : GlobalRuleSet) (n : RuleName) : Bool :=
  rs.toBaseRuleSet.contains n ||
  (n.builder == .simp && n.scope == .global &&
    SimpTheorems.containsDecl rs.simpTheorems n.name)

def LocalRuleSet.containsGlobalSimpTheorem (rs : LocalRuleSet) (decl : Name) :
    Bool :=
  rs.simpTheoremsArray.any λ (_, simpTheorems) =>
    SimpTheorems.containsDecl simpTheorems decl

def LocalRuleSet.contains (rs : LocalRuleSet) (n : RuleName) : Bool :=
  rs.toBaseRuleSet.contains n ||
  (n.builder == .simp &&
    match n.scope with
    | .global => rs.containsGlobalSimpTheorem n.name
    | .local  => rs.localNormSimpRules.any (·.id == n.name))


def BaseRuleSet.merge (rs₁ rs₂ : BaseRuleSet) : BaseRuleSet where
  normRules := rs₁.normRules.merge rs₂.normRules
  unsafeRules := rs₁.unsafeRules.merge rs₂.unsafeRules
  safeRules := rs₁.safeRules.merge rs₂.safeRules
  unfoldRules := rs₁.unfoldRules.mergeWith rs₂.unfoldRules
    λ _ unfoldThm?₁ _ => unfoldThm?₁
  ruleNames :=
    rs₁.ruleNames.mergeWith rs₂.ruleNames λ _ ns₁ ns₂ =>
      ns₁ ++ ns₂
  erased :=
    -- Add the erased rules from `rs₁` to `init`, except those rules which are
    -- present (and not erased) in `rs₂`.
    let go (rs₁ rs₂ : BaseRuleSet) (init : PHashSet RuleName) :
        PHashSet RuleName :=
      rs₁.erased.fold (init := init) λ x n =>
        match rs₂.ruleNames.find? n.name with
        | none => x.insert n
        | some ns =>
          if ns.contains n then x else x.insert n
    go rs₂ rs₁ $ go rs₁ rs₂ {}


def BaseRuleSet.add (rs : BaseRuleSet) (r : BaseRuleSetMember) :
    BaseRuleSet :=
  let erased := rs.erased.erase r.name
  let name := r.name.name
  let ruleNames :=
    match rs.ruleNames.find? name with
    | none => rs.ruleNames.insert name $ .singleton r.name
    | some ns => rs.ruleNames.insert name $ ns.insert r.name
  let rs := { rs with erased, ruleNames }
  match r with
  | .normRule r =>
    { rs with normRules := rs.normRules.add r r.indexingMode }
  | .unsafeRule r =>
    { rs with unsafeRules := rs.unsafeRules.add r r.indexingMode }
  | .safeRule r =>
    { rs with safeRules := rs.safeRules.add r r.indexingMode }
  | .unfoldRule r =>
    { rs with unfoldRules := rs.unfoldRules.insert r.decl r.unfoldThm? }

def LocalRuleSet.add (rs : LocalRuleSet) :
    LocalRuleSetMember → LocalRuleSet
  | .global (.base m) => rs.modifyBase (·.add m)
  | .global (.normSimpRule r) =>
    let simpTheoremsArray :=
      rs.simpTheoremsArray.modify 0 λ (name, simpTheorems) =>
        let simpTheorems :=
          r.entries.foldl (init := simpTheorems) SimpTheorems.addSimpEntry
        (name, simpTheorems)
    let simpTheoremsArrayNonempty : 0 < simpTheoremsArray.size := by
      simp [simpTheoremsArray, Array.size_modify, rs.simpTheoremsArrayNonempty]
    { rs with simpTheoremsArray, simpTheoremsArrayNonempty }
  | .localNormSimpRule r =>
    { rs with localNormSimpRules := rs.localNormSimpRules.push r }


def BaseRuleSet.erase (rs : BaseRuleSet) (f : RuleFilter) :
    BaseRuleSet × Bool := Id.run do
  let some ns := rs.ruleNames.find? f.name
    | return (rs, false)
  let (toErase, toKeep) := ns.partition f.matches
  if toErase.isEmpty then
    return (rs, false)

  let ruleNames :=
    if toKeep.isEmpty then
      rs.ruleNames.erase f.name
    else
      rs.ruleNames.insert f.name toKeep

  let mut erased := rs.erased
  let mut unfoldRules := rs.unfoldRules
  for r in toErase do
    match r.builder with
    | .unfold => unfoldRules := unfoldRules.erase r.name
    | .tactic | .forward | .destruct | .constructors | .cases | .apply =>
      erased := erased.insert r
    | .simp => continue

  let res := { rs with ruleNames, erased, unfoldRules }
  return (res, true)

def GlobalRuleSet.erase (rs : GlobalRuleSet) (f : RuleFilter) :
    GlobalRuleSet × Bool := Id.run do
  let (rs, anyErased) := rs.onBase (·.erase f)
  if let some decl := f.matchesSimpTheorem? then
    if SimpTheorems.containsDecl rs.simpTheorems decl then
      let simpTheorems := rs.simpTheorems.eraseCore (.decl decl (inv := false))
      return ({ rs with simpTheorems := simpTheorems }, true)
  return (rs, anyErased)

def LocalRuleSet.erase (rs : LocalRuleSet) (f : RuleFilter) :
    LocalRuleSet × Bool := Id.run do
  let (rs, anyErased) := rs.onBase (·.erase f)
  let mut anyErased := anyErased
  let mut localNormSimpRules := rs.localNormSimpRules
  let mut simpTheoremsArray' :
      Σ' a : Array (Name × SimpTheorems), a.size = rs.simpTheoremsArray.size :=
    ⟨rs.simpTheoremsArray, rfl⟩
  if let some id := f.matchesLocalNormSimpRule? then
    if let some idx := localNormSimpRules.findIdx? (·.id == id) then
      localNormSimpRules := localNormSimpRules.eraseIdx idx
  if let some decl := f.matchesSimpTheorem? then
    for h : i in [:rs.simpTheoremsArray.size] do
      have i_valid : i < simpTheoremsArray'.fst.size := by
        simp_all [Membership.mem, simpTheoremsArray'.snd]
      let (name, simpTheorems) := simpTheoremsArray'.fst[i]
      if SimpTheorems.containsDecl simpTheorems decl then
        let origin := .decl decl (inv := false)
        simpTheoremsArray' :=
          ⟨simpTheoremsArray'.fst.set ⟨i, i_valid⟩
            (name, simpTheorems.eraseCore origin),
           by simp [simpTheoremsArray'.snd, Array.size_set]⟩
        anyErased := true
  let simpTheoremsArray := simpTheoremsArray'.fst
  let simpTheoremsArrayNonempty : 0 < simpTheoremsArray.size := by
    simp [simpTheoremsArray'.snd, rs.simpTheoremsArrayNonempty]
  let rs := { rs with
    localNormSimpRules, simpTheoremsArray, simpTheoremsArrayNonempty
  }
  return (rs, anyErased)


namespace LocalRuleSet

def applicableNormalizationRulesWith (rs : LocalRuleSet) (goal : MVarId)
    (include? : NormRule → Bool) : MetaM (Array (IndexMatchResult NormRule)) :=
  rs.normRules.applicableRules goal
    (λ rule => include? rule && !rs.isErased rule.name)

@[inline, always_inline]
def applicableNormalizationRules (rs : LocalRuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult NormRule)) :=
  rs.applicableNormalizationRulesWith goal (λ _ => true)

def applicableUnsafeRulesWith (rs : LocalRuleSet) (goal : MVarId)
    (include? : UnsafeRule → Bool) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  rs.unsafeRules.applicableRules goal
    (λ rule => include? rule && !rs.isErased rule.name)

@[inline, always_inline]
def applicableUnsafeRules (rs : LocalRuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  rs.applicableUnsafeRulesWith goal (λ _ => true)

def applicableSafeRulesWith (rs : LocalRuleSet) (goal : MVarId)
    (include? : SafeRule → Bool) :=
  rs.safeRules.applicableRules goal
    (λ rule => include? rule && !rs.isErased rule.name)

@[inline, always_inline]
def applicableSafeRules (rs : LocalRuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult SafeRule)) :=
  rs.applicableSafeRulesWith goal (include? := λ _ => true)

def unindex (rs : LocalRuleSet) (p : RuleName → Bool) : LocalRuleSet := {
  rs with
  normRules := rs.normRules.unindex (p ·.name)
  unsafeRules := rs.unsafeRules.unindex (p ·.name)
  safeRules := rs.safeRules.unindex (p ·.name)
}

end LocalRuleSet


@[inline, always_inline]
def unindexPredicate? (options : Options') : Option (RuleName → Bool) :=
  if options.destructProductsTransparency == .reducible then
    none
  else
    some λ n => n.name == `Aesop.BuiltinRules.destructProducts

def mkLocalRuleSet (rss : Array (GlobalRuleSet × Name × Name))
    (options : Options') : CoreM LocalRuleSet := do
  let mut result := ∅
  let simpTheorems ← getSimpTheorems
  let simprocs ← Simp.getSimprocs
  result := {
    toBaseRuleSet := ∅
    simpTheoremsArray :=
      if options.useDefaultSimpSet then
        Array.mkEmpty (rss.size + 1) |>.push (`_, simpTheorems)
      else
        Array.mkEmpty (rss.size + 1) |>.push (`_, {})
    simprocsArray :=
      if options.useDefaultSimpSet then
        Array.mkEmpty (rss.size + 1) |>.push (`_, simprocs)
      else
        Array.mkEmpty (rss.size + 1) |>.push ((`_, {}))
    simpTheoremsArrayNonempty := by split <;> simp
    simprocsArrayNonempty := by split <;> simp
    localNormSimpRules := ∅
  }
  for (rs, simpExtName, simprocExtName) in rss do
    result := { result with
      toBaseRuleSet := result.toBaseRuleSet.merge rs.toBaseRuleSet
      simpTheoremsArray :=
        result.simpTheoremsArray.push (simpExtName, rs.simpTheorems)
      simpTheoremsArrayNonempty := by simp [result.simpTheoremsArrayNonempty]
      simprocsArray :=
        result.simprocsArray.push (simprocExtName, rs.simprocs)
      simprocsArrayNonempty := by simp [result.simprocsArrayNonempty]
    }
  if let some p := unindexPredicate? options then
    return result.unindex p
  else
    return result

end Aesop
