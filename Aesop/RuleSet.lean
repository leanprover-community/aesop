/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule
import Aesop.RuleIndex

open Lean
open Lean.Meta

namespace Aesop

inductive RuleSetMember' τ
  | normRule (r : NormRule' τ)
  | normSimpEntry (e : SimpEntry)
  | unsafeRule (r : UnsafeRule' τ)
  | safeRule (r : SafeRule' τ)
  deriving Inhabited

abbrev RuleSetMember := RuleSetMember' RuleTacWithBuilderDescr
abbrev RuleSetMemberDescr := RuleSetMember' GlobalRuleTacBuilderDescr

namespace RuleSetMember'

def mapM [Monad m] (f : τ → m ι) : RuleSetMember' τ → m (RuleSetMember' ι)
  | normRule r => return normRule (← r.mapTacM f)
  | normSimpEntry e => return normSimpEntry e
  | unsafeRule r => return unsafeRule (← r.mapTacM f)
  | safeRule r => return safeRule (← r.mapTacM f)

def toDescr (r : RuleSetMember) : Option RuleSetMemberDescr :=
  OptionM.run $ r.mapM (·.descr)

def ofDescr (r : RuleSetMemberDescr) : MetaM RuleSetMember :=
  r.mapM (·.toRuleTacBuilder)

end RuleSetMember'


structure RuleSet where
  normRules : RuleIndex NormRule
  normSimpLemmas : SimpLemmas
  normSimpLemmaDescrs : Array SimpEntry
  unsafeRules : RuleIndex UnsafeRule
  safeRules : RuleIndex SafeRule
  deriving Inhabited

namespace RuleSet

open MessageData in
instance : ToMessageData RuleSet where
  toMessageData rs :=
    "Aesop rule set:" ++ node #[
      "Unsafe rules:" ++ toMessageData rs.unsafeRules,
      "Safe rules:" ++ toMessageData rs.safeRules,
      "Normalisation rules:" ++ toMessageData rs.normRules,
      "Normalisation simp lemmas:" ++ rs.normSimpLemmas.toMessageData
    ]

def empty : RuleSet where
  normRules := {}
  normSimpLemmas := {}
  normSimpLemmaDescrs := #[]
  unsafeRules := {}
  safeRules := {}

instance : EmptyCollection RuleSet :=
  ⟨empty⟩

def merge (rs₁ rs₂ : RuleSet) : RuleSet where
  normRules := rs₁.normRules ++ rs₂.normRules
  normSimpLemmas := rs₁.normSimpLemmas.merge rs₂.normSimpLemmas
  normSimpLemmaDescrs := rs₁.normSimpLemmaDescrs ++ rs₂.normSimpLemmaDescrs
  unsafeRules := rs₁.unsafeRules ++ rs₂.unsafeRules
  safeRules := rs₁.safeRules ++ rs₂.safeRules

instance : Append RuleSet :=
  ⟨merge⟩

open RuleSetMember' in
def add (rs : RuleSet) : RuleSetMember → RuleSet
  | normRule r =>
    { rs with normRules := rs.normRules.add r r.indexingMode }
  | normSimpEntry e =>
    { rs with
      normSimpLemmas := rs.normSimpLemmas.addSimpEntry e
      normSimpLemmaDescrs := rs.normSimpLemmaDescrs.push e }
  | unsafeRule r =>
    { rs with unsafeRules := rs.unsafeRules.add r r.indexingMode }
  | safeRule r =>
    { rs with safeRules := rs.safeRules.add r r.indexingMode }

def addArray (rs : RuleSet) (ra : Array RuleSetMember) : RuleSet :=
  ra.foldl add rs

def applicableNormalizationRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult NormRule)) :=
  rs.normRules.applicableRules Rule'.compareByPriorityThenName goal

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult UnsafeRule)) :=
  rs.unsafeRules.applicableRules Rule'.compareByPriorityThenName goal

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
    MetaM (Array (IndexMatchResult SafeRule)) :=
  rs.safeRules.applicableRules Rule'.compareByPriorityThenName goal

def foldM [Monad m] (rs : RuleSet) (f : σ → RuleSetMember → m σ) (init : σ) :
    m σ := do
  match rs with
  | { normRules, safeRules, unsafeRules, normSimpLemmas := _, normSimpLemmaDescrs } =>
    let mut s := init
    s ← normRules.foldM   (init := s) λ s r => f s (RuleSetMember'.normRule r)
    s ← safeRules.foldM   (init := s) λ s r => f s (RuleSetMember'.safeRule r)
    s ← unsafeRules.foldM (init := s) λ s r => f s (RuleSetMember'.unsafeRule r)
    s ← normSimpLemmaDescrs.foldlM (init := s) λ s r =>
          f s (RuleSetMember'.normSimpEntry r)
    return s

@[inline]
def fold (rs : RuleSet) (f : σ → RuleSetMember → σ) (init : σ) : σ :=
  Id.run $ rs.foldM (init := init) f

end RuleSet


abbrev RuleSetName := Name -- Not really an abbreviation is it?

def defaultRuleSetName : RuleSetName := `default

def builtinRuleSetName : RuleSetName := `builtin

def defaultEnabledRuleSets : Array RuleSetName :=
  #[defaultRuleSetName, builtinRuleSetName]

structure RuleSets where
  default : RuleSet
  others : Std.PersistentHashMap Name RuleSet
  deriving Inhabited

namespace RuleSets

def empty : RuleSets where
  default := {}
  others := Std.PersistentHashMap.empty.insert builtinRuleSetName {}

instance : EmptyCollection RuleSets :=
  ⟨empty⟩

def add (rss : RuleSets) (name : RuleSetName) (r : RuleSetMember) : RuleSets :=
  if name == defaultRuleSetName then
    { rss with default := rss.default.add r }
  else
    { rss with
      others :=
        rss.others.insertWith name ⟨λ _ => RuleSet.empty.add r⟩
          (λ rs => rs.add r) }

def addArray (rss : RuleSets) (rules : Array (RuleSetName × RuleSetMember)) :
    RuleSets :=
  rules.foldl (init := rss) λ rss (r, name) => rss.add r name

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

-- If a rule set with name `rsName` already exists, it is overwritten.
-- Precondition: `rsName ≠ defaultRuleSetName`.
def addEmptyRuleSet (rss : RuleSets) (rsName : RuleSetName) : RuleSets :=
  { rss with others := rss.others.insert rsName {} }

def contains (rss : RuleSets) (name : RuleSetName) : Bool :=
  name == defaultRuleSetName || rss.others.contains name

-- Precondition: all rule set members in `rss` have a `RuleSetMemberDescr`.
def toDescrArray! (rss : RuleSets) :
    Array (RuleSetName × RuleSetMemberDescr) := Id.run do
  let mut s := #[]
  s := addRuleSetMembers s rss.default
  s := rss.others.foldl (init := s) λ s _ rs => addRuleSetMembers s rs
  return s
  where
    addRuleSetMembers (s : Array (RuleSetName × RuleSetMemberDescr))
        (rs : RuleSet) : Array (RuleSetName × RuleSetMemberDescr) :=
      rs.fold (init := s) λ s r =>
        let descr := r.toDescr.getD $ panic!
          "aesop: trying to serialise a rule set where not every rule has a RuleSetMemberDescr"
        s.push (defaultRuleSetName, descr)

end Aesop.RuleSets
