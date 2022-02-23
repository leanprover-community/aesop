/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule
import Aesop.RuleIndex

open Lean
open Lean.Meta
open Std (HashMap HashSet)

namespace Aesop

inductive RuleSetMember' τ
  | normRule (r : NormRule' τ)
  | normSimpRule (e : NormSimpRule)
  | unsafeRule (r : UnsafeRule' τ)
  | safeRule (r : SafeRule' τ)
  deriving Inhabited

abbrev RuleSetMember := RuleSetMember' RuleTacWithBuilderDescr
abbrev RuleSetMemberDescr := RuleSetMember' GlobalRuleTacBuilderDescr

namespace RuleSetMember'

def mapM [Monad m] (f : τ → m ι) : RuleSetMember' τ → m (RuleSetMember' ι)
  | normRule r => return normRule (← r.mapTacM f)
  | normSimpRule e => return normSimpRule e
  | unsafeRule r => return unsafeRule (← r.mapTacM f)
  | safeRule r => return safeRule (← r.mapTacM f)

def toDescr (r : RuleSetMember) : Option RuleSetMemberDescr :=
  OptionM.run $ r.mapM (·.descr)

def ofDescr (r : RuleSetMemberDescr) : MetaM RuleSetMember :=
  r.mapM (·.toRuleTacBuilder)

def name : RuleSetMember' τ → RuleName
  | normRule r => r.name
  | unsafeRule r => r.name
  | safeRule r => r.name
  | normSimpRule e => e.name

end RuleSetMember'


structure RuleNameFilter where
  ident : RuleIdent
  builders : Array BuilderName -- `#[]` means 'match any builder'
  phases : Array PhaseName     -- `#[]` means 'match any phase'

namespace RuleNameFilter

def «match» (f : RuleNameFilter) (n : RuleName) : Bool :=
  f.ident.name == n.name &&
  f.ident.scope == n.scope &&
  (f.builders.isEmpty || f.builders.any (· == n.builder)) &&
  (f.phases.isEmpty || f.phases.any (· == n.phase))

end RuleNameFilter


structure RuleSet where
  normRules : RuleIndex NormRule
  normSimpLemmas : SimpTheorems
  unsafeRules : RuleIndex UnsafeRule
  safeRules : RuleIndex SafeRule
  normSimpLemmaDescrs : HashMap RuleName (Array SimpEntry)
    -- A cache of the norm simp rules added to `normSimpLemmas`. Invariant: the
    -- simp entries in this map are a subset of those in `normSimpLemmas`. When
    -- a rule is erased, its entry is removed from this map. We use this map (a)
    -- to figure out which `SimpEntry`s to erase from `normSimpLemmas` when a
    -- rule is erased; (b) to serialise the norm simp rules.
  ruleNames : HashMap RuleIdent (Array RuleName)
    -- A cache of (non-erased) rule names. Invariant: `ruleNames` contains
    -- exactly the names of the rules in `normRules`, `normSimpLemmaDescrs`,
    -- `unsafeRules` and `safeRules`, minus the rules in `erased`. We use this
    -- cache to quickly determine whether a rule is present in the rule set.
  erased : HashSet RuleName
    -- A collection of erased rules. When we erase a rule -- or a family of
    -- rules, e.g. all rules associated with a certain declaration --, we do not
    -- remove them from `normRules`, `normSimpLemmas` etc. Instead, we add them
    -- to the `erased` set and remove them from `ruleNames`.
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
  ruleNames := {}
  erased := {}

instance : EmptyCollection RuleSet :=
  ⟨empty⟩

def merge (rs₁ rs₂ : RuleSet) : RuleSet where
  normRules := rs₁.normRules ++ rs₂.normRules
  normSimpLemmas := rs₁.normSimpLemmas.merge rs₂.normSimpLemmas
  unsafeRules := rs₁.unsafeRules ++ rs₂.unsafeRules
  safeRules := rs₁.safeRules ++ rs₂.safeRules
  normSimpLemmaDescrs :=
    rs₁.normSimpLemmaDescrs.merge rs₂.normSimpLemmaDescrs λ _ nsd₁ nsd₂ => nsd₁
    -- We can merge left-biased here because `nsd₁` and `nsd₂` should be equal
    -- anyway.
  ruleNames :=
    rs₁.ruleNames.merge rs₂.ruleNames λ _ ns₁ ns₂ =>
      ns₁.mergeUnsortedFilteringDuplicates ns₂
  erased :=
    -- Add the erased rules from `rs₁` to `init`, except those rules which are
    -- present (and not erased) in `rs₂`.
    let go (rs₁ rs₂ : RuleSet) (init : HashSet RuleName) : HashSet RuleName :=
      rs₁.erased.fold (init := init) λ x n =>
        match rs₂.ruleNames.find? n.toRuleIdent with
        | none => x.insert n
        | some ns =>
          if ns.contains n then x else x.insert n
    go rs₂ rs₁ $ go rs₁ rs₂ {}

instance : Append RuleSet :=
  ⟨merge⟩

open RuleSetMember' in
def add (rs : RuleSet) (r : RuleSetMember) : RuleSet :=
  let n := r.name
  let erased := rs.erased.erase n
  let ruleNames := rs.ruleNames.insertWith n.toRuleIdent #[n] λ ns =>
    if ns.contains n then ns else ns.push n
  let rs := { rs with erased := erased, ruleNames := ruleNames }
  match r with
  | normRule r =>
    { rs with normRules := rs.normRules.add r r.indexingMode }
  | normSimpRule r =>
    { rs with
      normSimpLemmas :=
        r.entries.foldl (init := rs.normSimpLemmas) λ simpLemmas e =>
          simpLemmas.addSimpEntry e
      normSimpLemmaDescrs := rs.normSimpLemmaDescrs.insert r.name r.entries }
  | unsafeRule r =>
    { rs with unsafeRules := rs.unsafeRules.add r r.indexingMode }
  | safeRule r =>
    { rs with safeRules := rs.safeRules.add r r.indexingMode }

def addArray (rs : RuleSet) (ra : Array RuleSetMember) : RuleSet :=
  ra.foldl add rs

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
      let res := { rs with
        ruleNames := ruleNames
        erased := erased
        normSimpLemmas := normSimpLemmas
        normSimpLemmaDescrs := normSimpLemmaDescrs
      }
      return (res, true)

def eraseAllRulesWithIdent (rs : RuleSet) (i : RuleIdent) : RuleSet × Bool :=
  rs.erase { ident := i, builders := #[], phases := #[] }

private def isErased (rs : RuleSet) (n : RuleName) : Bool :=
  rs.erased.contains n

def contains (rs : RuleSet) (n : RuleName) : Bool :=
  match rs.ruleNames.find? n.toRuleIdent with
  | none => false
  | some ns => ns.contains n

def applicableNormalizationRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult NormRule)) :=
  rs.normRules.applicableRules goal Rule'.compareByPriorityThenName
    (!rs.isErased ·.name)

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult UnsafeRule)) := do
  rs.unsafeRules.applicableRules goal Rule'.compareByPriorityThenName
    (!rs.isErased ·.name)

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult SafeRule)) := do
  rs.safeRules.applicableRules goal Rule'.compareByPriorityThenName
    (!rs.isErased ·.name)

def foldM [Monad m] (rs : RuleSet) (f : σ → RuleSetMember → m σ) (init : σ) :
    m σ := do
  let mut s := init
  s ← rs.normRules.foldM           (init := s) λ s r => go s (RuleSetMember'.normRule r)
  s ← rs.safeRules.foldM           (init := s) λ s r => go s (RuleSetMember'.safeRule r)
  s ← rs.unsafeRules.foldM         (init := s) λ s r => go s (RuleSetMember'.unsafeRule r)
  s ← rs.normSimpLemmaDescrs.foldM (init := s) λ s n es =>
        f s (RuleSetMember'.normSimpRule { name := n, entries := es })
        -- Erased rules are removed from `normSimpLemmaDescrs`, so we do not
        -- need to filter here.
  return s
  where
    @[inline]
    go (s : σ) (r : RuleSetMember) : m σ :=
      if rs.erased.contains r.name then pure s else f s r

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

def defaultEnabledRuleSets : Array RuleSetName :=
  #[defaultRuleSetName, builtinRuleSetName]


structure RuleSetNameFilter where
  ruleSetNames : Array Name -- #[] means 'match any rule set'

namespace RuleSetNameFilter

def «match» (f : RuleSetNameFilter) (n : RuleSetName) : Bool :=
  f.ruleSetNames.isEmpty || f.ruleSetNames.contains n

end RuleSetNameFilter


structure RuleSets where
  default : RuleSet
  others : Std.PersistentHashMap Name RuleSet
  deriving Inhabited

namespace RuleSets

protected def empty : RuleSets where
  default := {}
  others := Std.PersistentHashMap.empty.insert builtinRuleSetName {}

instance : EmptyCollection RuleSets :=
  ⟨RuleSets.empty⟩

open MessageData in
instance : ToMessageData RuleSets where
  toMessageData rss :=
    let printRuleSet rsName rs := m!"{rsName}:{indentD $ toMessageData rs}"
    let cmp (x y : RuleSetName × RuleSet) : Bool := x.fst.cmp y.fst |>.isLT
    unlines $
      #[ printRuleSet defaultRuleSetName rss.default ] ++
      (rss.others.toArray.qsort cmp |>.map λ (rsName, rs) =>
        printRuleSet rsName rs)

-- If a rule set with name `rsName` already exists, it is overwritten.
-- Precondition: `rsName ≠ defaultRuleSetName`.
def addEmptyRuleSet (rss : RuleSets) (rsName : RuleSetName) : RuleSets :=
  { rss with others := rss.others.insert rsName {} }

def containsRuleSet (rss : RuleSets) (name : RuleSetName) : Bool :=
  name == defaultRuleSetName || rss.others.contains name

-- Precondition: `rsName ≠ defaultRuleSetName`. The default rule set cannot be
-- erased. If `rss` does not contain a rule set with name `rsName`, `rss` is
-- returned unchanged.
def eraseRuleSet (rss : RuleSets) (rsName : RuleSetName) : RuleSets :=
  { rss with others := rss.others.erase rsName }

def getRuleSet? (rss : RuleSets) (rsName : RuleSetName) : Option RuleSet :=
  if rsName == defaultRuleSetName then rss.default else rss.others.find? rsName

-- If `rss` does not contain a rule set with name `rsName`, `rss` is returned
-- unchanged.
def modifyRuleSetM [Monad m] (rss : RuleSets) (rsName : RuleSetName)
    (f : RuleSet → m RuleSet) : m RuleSets := do
  if rsName == defaultRuleSetName then
    return { rss with default := ← f rss.default }
  else
    let (some rs) := rss.others.find? rsName | return rss
    return { rss with others := rss.others.insert rsName (← f rs) }

-- If `rss` does not contain a rule set with name `rsName`, `rss` is returned
-- unchanged.
def modifyRuleSet (rss : RuleSets) (rsName : RuleSetName)
    (f : RuleSet → RuleSet) : RuleSets :=
  Id.run $ rss.modifyRuleSetM rsName (λ rs => pure $ f rs)

def containsRule (rss : RuleSets) (rsName : RuleSetName) (rName : RuleName) :
    Bool :=
  match rss.getRuleSet? rsName with
  | none => false
  | some rs => rs.contains rName

-- Precondition: a rule set with name `rsName` exists in `rss`.
def addRule (rss : RuleSets) (rsName : RuleSetName) (r : RuleSetMember) :
    RuleSets :=
  rss.modifyRuleSet rsName (·.add r)

def addRuleChecked [Monad m] [MonadError m] (rss : RuleSets)
    (rsName : RuleSetName) (rule : RuleSetMember) : m RuleSets := do
  if ! rss.containsRuleSet rsName then throwError
    "aesop: no such rule set: '{rsName}'\n  (Use 'declare_aesop_rule_set' to declare rule sets.)"
  if rss.containsRule rsName rule.name then throwError
    "aesop: '{rule.name.name}' is already registered in rule set '{rsName}'"
  return rss.addRule rsName rule

-- Returns the updated rule sets and `true` if at least one rule was erased
-- (from at least one rule set).
def eraseRules (rss : RuleSets) (rsf : RuleSetNameFilter) (rf : RuleNameFilter) :
    RuleSets × Bool := Id.run do
  let mut result := rss
  let mut erased := false
  if rsf.match defaultRuleSetName then
    let (defaultRs, defaultErased) := rss.default.erase rf
    if defaultErased then
      result := { result with default := defaultRs }
      erased := true
  for (rsName, rs) in rss.others do
    if rsf.match rsName then
      let (rs, rsErased) := rs.erase rf
      if rsErased then
        result := { result with others := result.others.insert rsName rs }
        erased := true
  return (result, erased)

def eraseRulesChecked [Monad m] [MonadError m] (rss : RuleSets)
    (rsf : RuleSetNameFilter) (rf : RuleNameFilter) : m RuleSets := do
  let (rss, anyErased) := rss.eraseRules rsf rf
  unless anyErased do
    let rsNames := rsf.ruleSetNames
    if rsNames.isEmpty then
      throwError "aesop: '{rf.ident.name}' is not registered (with the given features) in any rule set."
    else
      throwError "aesop: '{rf.ident.name}' is not registered (with the given features) in any of the rule sets {String.joinSep ", " $ rsNames.map toString}."
  return rss

-- If a name in `rsNames` does not appear in `rss`, it is silently skipped.
def makeMergedRuleSet (rss : RuleSets)
    (rsNames : Array RuleSetName) : RuleSet := Id.run do
  let mut result :=
    if rsNames.contains defaultRuleSetName then rss.default else {}
  for name in rsNames do
    if name == defaultRuleSetName then
      continue
    match rss.others.find? name with
    | none => continue
    | some rs => result := result ++ rs
  return result

-- Precondition: all rule set members in `rss` have a `RuleSetMemberDescr`.
def toDescrArray! (rss : RuleSets) :
    Array (RuleSetName × RuleSetMemberDescr) := Id.run do
  let mut s := #[]
  s := addRuleSetMembers s defaultRuleSetName rss.default
  s := rss.others.foldl (init := s) λ s rsName rs =>
    addRuleSetMembers s rsName rs
  return s
  where
    addRuleSetMembers (s : Array (RuleSetName × RuleSetMemberDescr))
        (rsName : RuleSetName) (rs : RuleSet) :
        Array (RuleSetName × RuleSetMemberDescr) :=
      rs.fold (init := s) λ s r =>
        let descr := r.toDescr.getD $ panic!
          "aesop: trying to serialise a rule set where not every rule has a RuleSetMemberDescr"
        s.push (rsName, descr)

end Aesop.RuleSets
