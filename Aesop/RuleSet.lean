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
  | normSimpEntries (es : Array SimpEntry)
  | unsafeRule (r : UnsafeRule' τ)
  | safeRule (r : SafeRule' τ)
  deriving Inhabited

abbrev RuleSetMember := RuleSetMember' SerializableRuleTac
abbrev RuleSetMemberDescr := RuleSetMember' RuleTacDescr

namespace RuleSetMember'

def map (f : τ → ι) : RuleSetMember' τ → RuleSetMember' ι
  | normRule r => normRule (r.mapTac f)
  | normSimpEntries e => normSimpEntries e
  | unsafeRule r => unsafeRule (r.mapTac f)
  | safeRule r => safeRule (r.mapTac f)

def mapM [Monad m] (f : τ → m ι) : RuleSetMember' τ → m (RuleSetMember' ι)
  | normRule r => return normRule (← r.mapTacM f)
  | normSimpEntries e => normSimpEntries e
  | unsafeRule r => return unsafeRule (← r.mapTacM f)
  | safeRule r => return safeRule (← r.mapTacM f)

def toDescr (r : RuleSetMember) : Option RuleSetMemberDescr :=
  OptionM.run $ r.mapM (·.descr)

def ofDescr (r : RuleSetMemberDescr) : MetaM RuleSetMember :=
  r.mapM (·.toRuleTac)

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

def empty : RuleSet where
  normRules := RuleIndex.empty
  normSimpLemmas := {}
  unsafeRules := RuleIndex.empty
  safeRules := RuleIndex.empty

instance : EmptyCollection RuleSet :=
  ⟨empty⟩

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
  rs.normRules.applicableRules goal

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array (IndexMatchResult UnsafeRule)) :=
  rs.unsafeRules.applicableRules goal

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array (IndexMatchResult SafeRule)) :=
  rs.safeRules.applicableRules goal

end Aesop.RuleSet
