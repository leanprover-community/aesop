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
open Std (PHashMap HashSet)

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
  erased : HashSet RuleName
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
        (rs.localNormSimpLemmas.map (·.originalFVarUserName)),
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
    rs₁.normSimpLemmaDescrs.merge rs₂.normSimpLemmaDescrs λ _ nsd₁ nsd₂ => nsd₁
    -- We can merge left-biased here because `nsd₁` and `nsd₂` should be equal
    -- anyway.
  localNormSimpLemmas := rs₁.localNormSimpLemmas ++ rs₂.localNormSimpLemmas
  ruleNames :=
    rs₁.ruleNames.merge rs₂.ruleNames λ _ ns₁ ns₂ =>
      ns₁ ++ ns₂
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

def add (rs : RuleSet) (r : RuleSetMember) : RuleSet :=
  let n := r.name
  let erased := rs.erased.erase n
  let ruleNames := rs.ruleNames.insertWith n.toRuleIdent (.singleton n) λ ns =>
    if ns.contains n then ns else ns.insert n
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
  rs.erase { ident := i, builders := #[], phases := #[] }

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

def localRuleSetName : RuleSetName := `local

def defaultEnabledRuleSets : Array RuleSetName :=
  #[defaultRuleSetName, builtinRuleSetName, localRuleSetName]

def RuleSetName.isReserved (n : RuleSetName) : Bool :=
  n == defaultRuleSetName || n == builtinRuleSetName || n == localRuleSetName


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
  others :=
    Std.PersistentHashMap.empty
    |>.insert builtinRuleSetName {}
    |>.insert localRuleSetName {}

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

@[inline]
def foldM [Monad m] (f : σ → RuleSetName → RuleSet → m σ) (init : σ)
    (rss : RuleSets) : m σ := do
  let acc ← f init defaultRuleSetName rss.default
  rss.others.foldlM (init := acc) f

@[inline]
def fold (f : σ → RuleSetName → RuleSet → σ) (init : σ) (rss : RuleSets) : σ :=
  Id.run $ foldM f init rss

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
    | some rs => result := result.merge rs
  return result

def globalRules (rss : RuleSets) : Array (RuleSetName × RuleSetMember) :=
  rss.fold (init := #[]) λ acc rsName rs =>
    rs.fold (init := acc) λ acc r =>
      if r.isGlobal then
        acc.push (rsName, r)
      else
        acc

end Aesop.RuleSets
