/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder
import Aesop.Index
import Aesop.Rule

open Lean
open Lean.Meta

namespace Aesop

inductive RuleSetMember
  | normRule (r : NormRule)
  | unsafeRule (r : UnsafeRule)
  | safeRule (r : SafeRule)
  | normSimpRule (r : NormSimpRule)
  | localNormSimpRule (r : LocalNormSimpRule)
  deriving Inhabited

namespace RuleSetMember

def name : RuleSetMember → RuleName
  | normRule r => r.name
  | unsafeRule r => r.name
  | safeRule r => r.name
  | normSimpRule r => r.name
  | localNormSimpRule r => r.name

def isGlobal (m : RuleSetMember) : Bool :=
  m.name.scope == .global

end RuleSetMember


structure RuleNameFilter where
  ident : RuleIdent
  builders : Array BuilderName -- `#[]` means 'match any builder'
  phases : Array PhaseName     -- `#[]` means 'match any phase'

namespace RuleNameFilter

def ofIdent (i : RuleIdent) : RuleNameFilter where
  ident := i
  builders := #[]
  phases := #[]

def «match» (f : RuleNameFilter) (n : RuleName) : Bool :=
  f.ident.name == n.name &&
  f.ident.scope == n.scope &&
  (f.builders.isEmpty || f.builders.any (· == n.builder)) &&
  (f.phases.isEmpty || f.phases.any (· == n.phase))

end RuleNameFilter


structure RuleSet where
  normRules : Index NormRule
  unsafeRules : Index UnsafeRule
  safeRules : Index SafeRule
  normSimpLemmas : SimpTheorems
  normSimpLemmaDescrs : PHashMap RuleName (Array SimpEntry)
    -- A cache of the norm simp rules added to `normSimpLemmas`. Invariant: the
    -- simp entries in this map are a subset of those in `normSimpLemmas`. When
    -- a rule is erased, its entry is removed from this map. We use this map (a)
    -- to figure out which `SimpEntry`s to erase from `normSimpLemmas` when a
    -- rule is erased; (b) to serialise the norm simp rules.
  localNormSimpLemmas : Array LocalNormSimpRule
    -- This does not need to be persistent because the global rule set (which is
    -- stored in an env extension and should therefore be persistent) never
    -- contains local norm simp lemmas.
  ruleNames : PHashMap RuleIdent (UnorderedArraySet RuleName)
    -- A cache of (non-erased) rule names. Invariant: `ruleNames` contains
    -- exactly the names of the rules in `normRules`, `normSimpLemmaDescrs`,
    -- `unsafeRules` and `safeRules`, minus the rules in `erased`. We use this
    -- cache to quickly determine whether a rule is present in the rule set.
  erased : PHashSet RuleName
    -- The set of rules that were erased from `normRules`, `unsafeRules` and
    -- `safeRules`. When erasing a rule which is present in any of these three
    -- indices, the rule is not removed from the indices but just added to this
    -- set.
  deriving Inhabited

namespace RuleSet

open MessageData in
instance : ToMessageData RuleSet where
  toMessageData rs :=
    unlines #[
      "Unsafe rules:" ++ toMessageData rs.unsafeRules,
      "Safe rules:" ++ toMessageData rs.safeRules,
      "Normalisation rules:" ++ toMessageData rs.normRules,
      "Normalisation simp lemmas:" ++ rs.normSimpLemmas.toMessageData,
      "Local normalisation simp lemmas:" ++ .node
        (rs.localNormSimpLemmas.map (·.fvarUserName)),
      "Erased rules:" ++ indentD (unlines $
        rs.erased.toArray.qsort (λ x y => compare x y |>.isLT)
          |>.map toMessageData)
    ]

def empty : RuleSet where
  normRules := {}
  normSimpLemmas := {}
  unsafeRules := {}
  safeRules := {}
  normSimpLemmaDescrs := {}
  localNormSimpLemmas := {}
  ruleNames := {}
  erased := {}

instance : EmptyCollection RuleSet :=
  ⟨empty⟩

def merge (rs₁ rs₂ : RuleSet) : RuleSet where
  normRules := rs₁.normRules.merge rs₂.normRules
  normSimpLemmas := rs₁.normSimpLemmas.merge rs₂.normSimpLemmas
  unsafeRules := rs₁.unsafeRules.merge rs₂.unsafeRules
  safeRules := rs₁.safeRules.merge rs₂.safeRules
  normSimpLemmaDescrs :=
    rs₁.normSimpLemmaDescrs.mergeWith rs₂.normSimpLemmaDescrs λ _ nsd₁ _ => nsd₁
    -- We can merge left-biased here because `nsd₁` and `nsd₂` should be equal
    -- anyway.
  localNormSimpLemmas := rs₁.localNormSimpLemmas ++ rs₂.localNormSimpLemmas
  ruleNames :=
    rs₁.ruleNames.mergeWith rs₂.ruleNames λ _ ns₁ ns₂ =>
      ns₁ ++ ns₂
  erased :=
    -- Add the erased rules from `rs₁` to `init`, except those rules which are
    -- present (and not erased) in `rs₂`.
    let go (rs₁ rs₂ : RuleSet) (init : PHashSet RuleName) : PHashSet RuleName :=
      rs₁.erased.fold (init := init) λ x n =>
        match rs₂.ruleNames.find? n.toRuleIdent with
        | none => x.insert n
        | some ns =>
          if ns.contains n then x else x.insert n
    go rs₂ rs₁ $ go rs₁ rs₂ {}

def add (rs : RuleSet) (r : RuleSetMember) : RuleSet :=
  let n := r.name
  let erased := rs.erased.erase n
  let ruleNames :=
    let ident := n.toRuleIdent
    match rs.ruleNames.find? ident with
    | none => rs.ruleNames.insert ident $ .singleton n
    | some ns => rs.ruleNames.insert ident $ ns.insert n
  let rs := { rs with erased := erased, ruleNames := ruleNames }
  match r with
  | .normRule r =>
    { rs with normRules := rs.normRules.add r r.indexingMode }
  | .unsafeRule r =>
    { rs with unsafeRules := rs.unsafeRules.add r r.indexingMode }
  | .safeRule r =>
    { rs with safeRules := rs.safeRules.add r r.indexingMode }
  | .normSimpRule r =>
    { rs with
      normSimpLemmas :=
        r.entries.foldl (init := rs.normSimpLemmas) λ simpLemmas e =>
          simpLemmas.addSimpEntry e
      normSimpLemmaDescrs := rs.normSimpLemmaDescrs.insert r.name r.entries }
  | .localNormSimpRule r =>
    { rs with localNormSimpLemmas := rs.localNormSimpLemmas.push r }

def addArray (rs : RuleSet) (ra : Array RuleSetMember) : RuleSet :=
  ra.foldl add rs

def rulesMatching (rs : RuleSet) (f : RuleNameFilter) :
    UnorderedArraySet RuleName :=
  match rs.ruleNames.find? f.ident with
  | none => ∅
  | some ns => ns.filter f.match

-- Returns the updated rule set and `true` if at least one rule was erased.
def erase (rs : RuleSet) (f : RuleNameFilter) : RuleSet × Bool :=
  match rs.ruleNames.find? f.ident with
  | none => (rs, false)
  | some ns =>
    let (toErase, toKeep) := ns.partition f.match
    if toErase.isEmpty then
      (rs, false)
    else Id.run do
      let ruleNames :=
        if toKeep.isEmpty then
          rs.ruleNames.erase f.ident
        else
          rs.ruleNames.insert f.ident toKeep

      let mut erased := rs.erased
      let mut normSimpLemmaDescrs := rs.normSimpLemmaDescrs
      let mut normSimpLemmas := rs.normSimpLemmas
      for r in toErase do
        erased := erased.insert r
        if let (some simpEntries) := normSimpLemmaDescrs.find? r then
          normSimpLemmaDescrs := normSimpLemmaDescrs.erase r
          for e in simpEntries do
            normSimpLemmas := normSimpLemmas.eraseSimpEntry e

      let localNormSimpLemmas := rs.localNormSimpLemmas.filter λ r =>
        ! toErase.contains r.name

      let res := {
        rs with
        ruleNames, erased, normSimpLemmas, normSimpLemmaDescrs,
        localNormSimpLemmas
      }
      return (res, true)

def eraseAllRulesWithIdent (rs : RuleSet) (i : RuleIdent) : RuleSet × Bool :=
  rs.erase (.ofIdent i)

@[inline]
private def isErased (rs : RuleSet) (n : RuleName) : Bool :=
  rs.erased.contains n

def contains (rs : RuleSet) (n : RuleName) : Bool :=
  ! rs.isErased n &&
  match rs.ruleNames.find? n.toRuleIdent with
  | none => false
  | some ns => ns.contains n

def applicableNormalizationRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult NormRule)) :=
  rs.normRules.applicableRules (ord := ⟨Rule.compareByPriorityThenName⟩) goal
    (!rs.isErased ·.name)

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  rs.unsafeRules.applicableRules (ord := ⟨Rule.compareByPriorityThenName⟩) goal
    (!rs.isErased ·.name)

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult SafeRule)) := do
  rs.safeRules.applicableRules (ord := ⟨Rule.compareByPriorityThenName⟩) goal
    (!rs.isErased ·.name)

def foldM [Monad m] (rs : RuleSet) (f : σ → RuleSetMember → m σ) (init : σ) :
    m σ := do
  let mut s := init
  s ← rs.normRules.foldM            (init := s) λ s r => go s (.normRule r)
  s ← rs.safeRules.foldM            (init := s) λ s r => go s (.safeRule r)
  s ← rs.unsafeRules.foldM          (init := s) λ s r => go s (.unsafeRule r)
  s ← rs.normSimpLemmaDescrs.foldlM (init := s) λ s n es =>
        f s (.normSimpRule { name := n, entries := es })
        -- Erased rules are removed from `normSimpLemmaDescrs`, so we do not
        -- need to filter here.
  return s
  where
    @[inline]
    go (s : σ) (r : RuleSetMember) : m σ :=
      if rs.isErased r.name then pure s else f s r

@[inline]
def fold (rs : RuleSet) (f : σ → RuleSetMember → σ) (init : σ) : σ :=
  Id.run $ rs.foldM f init

-- TODO remove?
def foldGlobalRulesForDeclM [Monad m] (decl : Name) (rs : RuleSet)
    (f : σ → RuleSetMember → m σ) (init : σ) : m σ :=
  rs.foldM (init := init) λ s r =>
    match r.name.scope with
    | ScopeName.global => f s r
    | ScopeName.local => pure init

-- TODO remove?
@[inline]
def foldGlobalRulesForDecl (decl : Name) (rs : RuleSet)
    (f : σ → RuleSetMember → σ) (init : σ) : σ :=
  Id.run $ rs.foldGlobalRulesForDeclM decl f init

end RuleSet


abbrev RuleSetName := Name -- Not really an abbreviation is it?

def defaultRuleSetName : RuleSetName := `default

def builtinRuleSetName : RuleSetName := `builtin

def localRuleSetName : RuleSetName := `local

def builtinRuleSetNames : Array RuleSetName :=
  #[defaultRuleSetName, builtinRuleSetName, localRuleSetName]

def defaultEnabledRuleSetNames := builtinRuleSetNames

def RuleSetName.isReserved (n : RuleSetName) : Bool :=
  builtinRuleSetNames.contains n

structure RuleSetNameFilter where
  ns : Array RuleSetName -- #[] means 'match any rule set'

namespace RuleSetNameFilter

protected def all : RuleSetNameFilter :=
  ⟨#[]⟩

def matchesAll (f : RuleSetNameFilter) : Bool :=
  f.ns.isEmpty

def «match» (f : RuleSetNameFilter) (n : RuleSetName) : Bool :=
  f.matchesAll || f.ns.contains n

def matchedRuleSetNames (f : RuleSetNameFilter) : Option (Array RuleSetName) :=
  if f.matchesAll then
    none
  else
    some f.ns

end RuleSetNameFilter


structure RuleSets where
  rs : HashMap RuleSetName RuleSet
  deriving Inhabited

namespace RuleSets

protected def empty : RuleSets where
  rs := ∅

instance : EmptyCollection RuleSets :=
  ⟨RuleSets.empty⟩

instance : ToMessageData RuleSets where
  toMessageData rss :=
    let lt (x y : RuleSetName × RuleSet) := x.fst.cmp y.fst |>.isLT
    .unlines $
      rss.rs.toArray.qsort lt |>.map λ (rsName, rs) =>
        m!"{rsName}:{indentD $ toMessageData rs}"

-- If a rule set with name `rsName` already exists, it is overwritten.
def addEmptyRuleSet (rss : RuleSets) (rsName : RuleSetName) : RuleSets :=
  ⟨rss.rs.insert rsName {}⟩

-- If a rule set with name `rsName` already exists, it is overwritten.
def addRuleSet (rss : RuleSets) (rsName : RuleSetName) (rs : RuleSet) :
    RuleSets :=
  ⟨rss.rs.insert rsName rs⟩

def containsRuleSet (rss : RuleSets) (name : RuleSetName) : Bool :=
  rss.rs.contains name

-- Adds the rule set `name` if it is not already present in `rss`.
def ensureRuleSet (rss : RuleSets) (name : RuleSetName) : RuleSets :=
  if rss.containsRuleSet name then
    rss
  else
    rss.addEmptyRuleSet name

-- If `rss` does not contain a rule set with name `rsName`, `rss` is
-- returned unchanged.
def eraseRuleSet (rss : RuleSets) (rsName : RuleSetName) : RuleSets :=
  ⟨rss.rs.erase rsName⟩

def getRuleSet? (rss : RuleSets) (rsName : RuleSetName) : Option RuleSet :=
  rss.rs.find? rsName

-- If `rss` does not contain a rule set with name `rsName`, `rss` is returned
-- unchanged.
@[inline]
def modifyRuleSetM [Monad m] (rss : RuleSets) (rsName : RuleSetName)
    (f : RuleSet → m RuleSet) : m RuleSets := do
  let (some rs) := rss.getRuleSet? rsName
    | return rss
  return ⟨rss.rs.insert rsName (← f rs)⟩

-- If `rss` does not contain a rule set with name `rsName`, `rss` is returned
-- unchanged.
@[inline]
def modifyRuleSet (rss : RuleSets) (rsName : RuleSetName)
    (f : RuleSet → RuleSet) : RuleSets :=
  Id.run $ rss.modifyRuleSetM rsName (λ rs => pure $ f rs)

def containsRule (rss : RuleSets) (rsName : RuleSetName) (rName : RuleName) :
    Bool :=
  match rss.getRuleSet? rsName with
  | none => false
  | some rs => rs.contains rName

-- Precondition: a rule set with name `rsName` exists in `rss`.
def addRuleUnchecked (rss : RuleSets) (rsName : RuleSetName) (r : RuleSetMember) :
    RuleSets :=
  rss.modifyRuleSet rsName (·.add r)

def addRuleChecked [Monad m] [MonadError m] (rss : RuleSets)
    (rsName : RuleSetName) (rule : RuleSetMember) : m RuleSets := do
  if ! rss.containsRuleSet rsName then throwError
    "aesop: no such rule set: '{rsName}'\n  (Use 'declare_aesop_rule_set' to declare rule sets.\n   Declared rule sets are not visible in the current file; they only become visible once you import the declaring file.)"
  if rss.containsRule rsName rule.name then throwError
    "aesop: rule '{rule.name.name}' is already registered in rule set '{rsName}'"
  return rss.addRuleUnchecked rsName rule

-- Returns the updated rule sets and `true` if at least one rule was erased
-- (from at least one rule set).
def eraseRules (rss : RuleSets) (rsf : RuleSetNameFilter)
    (rf : RuleNameFilter) : RuleSets × Bool :=
  rss.rs.fold (init := (rss, false)) λ (rss, anyErased) rsName rs =>
    if rsf.match rsName then
      let (rs, rsErased) := rs.erase rf
      if rsErased then
        (⟨rss.rs.insert rsName rs⟩, true)
      else
        (rss, anyErased)
    else
      (rss, anyErased)

def eraseRulesChecked [Monad m] [MonadError m] (rss : RuleSets)
    (rsf : RuleSetNameFilter) (rf : RuleNameFilter) : m RuleSets := do
  let (rss, anyErased) := rss.eraseRules rsf rf
  unless anyErased do
    let rsNames? := rsf.matchedRuleSetNames
    match rsNames? with
    | none => throwError "aesop: '{rf.ident.name}' is not registered (with the given features) in any rule set."
    | some rsNames => throwError "aesop: '{rf.ident.name}' is not registered (with the given features) in any of the rule sets {rsNames.map toString}."
  return rss

def getMergedRuleSet (rss : RuleSets) : RuleSet :=
  rss.rs.fold (init := ∅) λ result _ rs => result.merge rs

end Aesop.RuleSets
