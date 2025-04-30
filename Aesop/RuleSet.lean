/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Aesop.Index
import Aesop.Index.Forward
import Aesop.RuleSet.Filter
import Aesop.RuleSet.Member
import Aesop.Tree.Data.ForwardRuleMatches

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
  -- TODO Don't cache equation name; this may lead to bugs and the performance
  -- cost is negligible.
  unfoldRules : PHashMap Name (Option Name)
  /--
  Forward rules. There's a special procedure for applying forward rules, so we
  don't store them in the regular indices.
  -/
  forwardRules : ForwardIndex
  /-- The names of all rules in `forwardRules`. -/
  -- HACK to be removed once we switch fully to stateful forward reasoning.
  forwardRuleNames : PHashSet RuleName
  /--
  An index for the rule patterns associated with rules contained in this rule
  set. When rules are removed from the rule set, their patterns are not removed
  from this index.
  -/
  rulePatterns : RulePatternIndex
  /--
  The set of rules that were erased from `normRules`, `unsafeRules`, `safeRules`
  and `forwardRules`. When we erase a rule which is present in any of these four
  indices, the rule is not removed from the indices but just added to this set.
  By contrast, when we erase a rule from `unfoldRules`, we actually delete it.
  -/
  erased : PHashSet RuleName
  /--
  A cache of the names of all rules registered in this rule set. Invariant:
  `ruleNames` contains exactly the names of the rules present in `normRules`,
  `unsafeRules`, `safeRules`, `forwardRules` and `unfoldRules` and not present
  in `erased`. We use this cache (a) to quickly determine whether a rule is
  present in the rule set and (b) to find the full rule names associated with
  the fvar or const identified by a name.
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
  withConstAesopTraceNode traceOpt (return "Forward rules") do
    rs.forwardRules.trace traceOpt
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


def BaseRuleSet.empty : BaseRuleSet := by
  refine' {..} <;> exact {}

instance : EmptyCollection BaseRuleSet :=
  ⟨.empty⟩

def GlobalRuleSet.empty : GlobalRuleSet := by
  refine' {..} <;> exact {}

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
  forwardRules := rs₁.forwardRules.merge rs₂.forwardRules
  forwardRuleNames := rs₁.forwardRuleNames.merge rs₂.forwardRuleNames
  rulePatterns := rs₁.rulePatterns.merge rs₂.rulePatterns
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
    let rs := { rs with normRules := rs.normRules.add r r.indexingMode }
    addRulePattern r.name r.pattern? rs
  | .unsafeRule r =>
    let rs := { rs with unsafeRules := rs.unsafeRules.add r r.indexingMode }
    addRulePattern r.name r.pattern? rs
  | .safeRule r =>
    let rs := { rs with safeRules := rs.safeRules.add r r.indexingMode }
    addRulePattern r.name r.pattern? rs
  | .unfoldRule r =>
    { rs with unfoldRules := rs.unfoldRules.insert r.decl r.unfoldThm? }
  | .normForwardRule r₁ r₂ =>
    let rs := {
      rs with
      forwardRules := rs.forwardRules.insert r₁
      forwardRuleNames := rs.forwardRuleNames.insert r₁.name
      normRules := rs.normRules.add r₂ r₂.indexingMode
    }
    addRulePattern r₂.name r₂.pattern? rs
  | .unsafeForwardRule r₁ r₂ =>
    let rs := {
      rs with
      forwardRules := rs.forwardRules.insert r₁
      forwardRuleNames := rs.forwardRuleNames.insert r₁.name
      unsafeRules := rs.unsafeRules.add r₂ r₂.indexingMode
    }
    addRulePattern r₂.name r₂.pattern? rs
  | .safeForwardRule r₁ r₂ =>
    let rs := {
      rs with
      forwardRules := rs.forwardRules.insert r₁
      forwardRuleNames := rs.forwardRuleNames.insert r₁.name
      safeRules := rs.safeRules.add r₂ r₂.indexingMode
    }
    addRulePattern r₂.name r₂.pattern? rs
where
  addRulePattern (n : RuleName) (pat? : Option RulePattern)
      (rs : BaseRuleSet) : BaseRuleSet :=
    match pat? with
    | none => rs
    | some pat => { rs with rulePatterns := rs.rulePatterns.add n pat }

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
    if let some idx := localNormSimpRules.findFinIdx? (·.id == id) then
      localNormSimpRules := localNormSimpRules.eraseIdx idx
  if let some decl := f.matchesSimpTheorem? then
    for h : i in [:rs.simpTheoremsArray.size] do
      have i_valid : i < simpTheoremsArray'.fst.size := by
        simp_all +zetaDelta [Membership.mem, simpTheoremsArray'.snd]
      let (name, simpTheorems) := simpTheoremsArray'.fst[i]
      if SimpTheorems.containsDecl simpTheorems decl then
        let origin := .decl decl (inv := false)
        simpTheoremsArray' :=
          ⟨simpTheoremsArray'.fst.set i
            (name, simpTheorems.eraseCore origin),
           by simp [simpTheoremsArray'.snd, Array.size_set]⟩
        anyErased := true
  let simpTheoremsArray := simpTheoremsArray'.fst
  let simpTheoremsArrayNonempty : 0 < simpTheoremsArray.size := by
    simp [simpTheoremsArray, simpTheoremsArray'.snd, rs.simpTheoremsArrayNonempty]
  let rs := { rs with
    localNormSimpRules, simpTheoremsArray, simpTheoremsArrayNonempty
  }
  return (rs, anyErased)


namespace LocalRuleSet

@[inline, always_inline]
private def fwdRulePredicate (opts : Lean.Options) (rs : LocalRuleSet)
    (include? : Rule α → Bool) (r : Rule α) : Bool :=
  aesop.dev.statefulForward.get opts && include? r && ! rs.isErased r.name

@[inline, always_inline]
private def rulePredicate (opts : Lean.Options) (rs : LocalRuleSet)
    (include? : Rule α → Bool) : Rule α → Bool :=
  -- HACK When stateful forward reasoning is active, we exclude rules which are
  -- already covered by equivalent `ForwardRule`s.
  if aesop.dev.statefulForward.get opts then
    λ r => include? r && ! rs.isErased r.name &&
           ! rs.forwardRuleNames.contains r.name
  else
    λ r => include? r && ! rs.isErased r.name

private def postprocessForwardMatchRules (opts : Lean.Options) (rs : LocalRuleSet)
    (include? : Rule α → Bool) (rules : Array (Rule α)) :
    Array (IndexMatchResult (Rule α)) :=
  rules.filter (fwdRulePredicate opts rs include?) |>.map λ rule =>
    { rule, locations := ∅, patternSubsts? := none }

def applicableNormalizationRulesWith (rs : LocalRuleSet)
    (fms : ForwardRuleMatches) (goal : MVarId)
    (include? : NormRule → Bool) : BaseM (Array (IndexMatchResult NormRule)) := do
  let opts ← getOptions
  let normFwdRules := postprocessForwardMatchRules opts rs include? fms.normRules
  let patInstMap ← rs.rulePatterns.getInGoal goal
  rs.normRules.applicableRules goal patInstMap normFwdRules
    (rulePredicate opts rs include?)

@[inline, always_inline]
def applicableNormalizationRules (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) : BaseM (Array (IndexMatchResult NormRule)) :=
  rs.applicableNormalizationRulesWith fms goal (include? := λ _ => true)

def applicableUnsafeRulesWith (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) (include? : UnsafeRule → Bool) :
    BaseM (Array (IndexMatchResult UnsafeRule)) := do
  let opts ← getOptions
  let unsafeFwdRules := postprocessForwardMatchRules opts rs include? fms.unsafeRules
  let patInstMap ← rs.rulePatterns.getInGoal goal
  rs.unsafeRules.applicableRules goal patInstMap unsafeFwdRules
    (rulePredicate opts rs include?)

@[inline, always_inline]
def applicableUnsafeRules (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) : BaseM (Array (IndexMatchResult UnsafeRule)) :=
  rs.applicableUnsafeRulesWith fms goal (include? := λ _ => true)

def applicableSafeRulesWith (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) (include? : SafeRule → Bool) :
    BaseM (Array (IndexMatchResult SafeRule)) := do
  let opts ← getOptions
  let safeFwdRules := postprocessForwardMatchRules opts rs include? fms.safeRules
  let patInstMap ← rs.rulePatterns.getInGoal goal
  rs.safeRules.applicableRules goal patInstMap safeFwdRules
    (rulePredicate opts rs include?)

@[inline, always_inline]
def applicableSafeRules (rs : LocalRuleSet) (fms : ForwardRuleMatches)
    (goal : MVarId) : BaseM (Array (IndexMatchResult SafeRule)) :=
  rs.applicableSafeRulesWith fms goal (include? := λ _ => true)

def applicableForwardRulesWith (rs : LocalRuleSet) (e : Expr)
    (include? : ForwardRule → Bool) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  withConstAesopTraceNode .forward (return m!"selected forward rules:") do
    let rules ← rs.forwardRules.get e
    let rules := rules.filter λ (rule, _) =>
      include? rule && !rs.isErased rule.name
    aesop_trace[forward] do
      for (r, i) in rules do
        aesop_trace![forward] mkMsg r i
    return rules
  where
    mkMsg r i := m!"{r}, premise {i}" -- Inlining this triggers a Lean bug.

@[inline, always_inline]
def applicableForwardRules (rs : LocalRuleSet) (e : Expr) :
    MetaM (Array (ForwardRule × PremiseIndex)) :=
  rs.applicableForwardRulesWith e (include? := λ _ => true)

def constForwardRuleMatches (rs : LocalRuleSet) : Array ForwardRuleMatch :=
  rs.forwardRules.getConstRuleMatches

section ForwardRulePattern

private def postprocessPatSubstMap (rs : LocalRuleSet)
    (m : RulePatternSubstMap) : Array (ForwardRule × Substitution) :=
  m.toFlatArray.filterMap λ (n, patSubst) =>
    rs.forwardRules.getRuleWithName? n |>.map (·, patSubst)

def forwardRulePatternSubstsInExpr (rs : LocalRuleSet) (e : Expr) :
    BaseM (Array (ForwardRule × Substitution)) := do
  withConstAesopTraceNode .forward (return m!"rule patterns in expr {e}:") do
    let ms ← rs.rulePatterns.get e
    let ms := postprocessPatSubstMap rs ms
    aesop_trace[forward] do
      for (r, inst) in ms do
        aesop_trace![forward] m!"{r}, {inst}"
    return ms

def forwardRulePatternSubstsInLocalDecl (rs : LocalRuleSet) (ldecl : LocalDecl) :
    BaseM (Array (ForwardRule × Substitution)) := do
  withConstAesopTraceNode .forward (return m!"rule patterns in hyp {ldecl.userName}:") do
    let ms ← rs.rulePatterns.getInLocalDecl ldecl
    let ms := postprocessPatSubstMap rs ms
    aesop_trace[forward] do
      for (r, inst) in ms do
        aesop_trace![forward] m!"{r}, {inst}"
    return ms

end ForwardRulePattern

-- NOTE: only non-forward norm/safe/unsafe rules can be unindexed.
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
