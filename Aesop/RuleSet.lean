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
  | normSimpEntries (es : Array SimpEntry) -- TODO make this a single SimpEntry
  | unsafeRule (r : UnsafeRule' τ)
  | safeRule (r : SafeRule' τ)
  deriving Inhabited

abbrev RuleSetMember := RuleSetMember' RuleTacWithBuilderDescr
abbrev RuleSetMemberDescr := RuleSetMember' GlobalRuleTacBuilderDescr

namespace RuleSetMember'

def mapM [Monad m] (f : τ → m ι) : RuleSetMember' τ → m (RuleSetMember' ι)
  | normRule r => return normRule (← r.mapTacM f)
  | normSimpEntries e => return normSimpEntries e
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

instance : EmptyCollection RuleSet where
  emptyCollection := {
    normRules := {}
    normSimpLemmas := {}
    unsafeRules := {}
    safeRules := {}
  }

def merge (rs₁ rs₂ : RuleSet) : RuleSet where
  normRules := rs₁.normRules ++ rs₂.normRules
  normSimpLemmas := rs₁.normSimpLemmas.merge rs₂.normSimpLemmas
  unsafeRules := rs₁.unsafeRules ++ rs₂.unsafeRules
  safeRules := rs₁.safeRules ++ rs₂.safeRules

instance : Append RuleSet :=
  ⟨merge⟩

open RuleSetMember' in
def add (rs : RuleSet) : RuleSetMember → RuleSet
  | normRule r =>
    { rs with normRules := rs.normRules.add r r.indexingMode }
  | normSimpEntries es =>
    { rs with
      normSimpLemmas :=
        es.foldl (init := rs.normSimpLemmas) SimpLemmas.addSimpEntry }
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

end Aesop.RuleSet
