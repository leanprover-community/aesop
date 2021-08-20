/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Percent
import Aesop.RuleTac
import Aesop.Util

namespace Aesop

open Lean
open Lean.Meta
open Std (RBMap mkRBMap)


/-! ## Rule Indexing Modes -/

inductive IndexingMode : Type
  | unindexed
  | target (keys : Array DiscrTree.Key)
  | hyps (keys : Array DiscrTree.Key)
  deriving Inhabited, BEq


/-! ## Rules -/

/- The rules in a rule set should be uniquely identified by their name. -/
structure Rule' (α τ : Type) where
  name : Name
  indexingMode : IndexingMode
  extra : α
  tac : τ
  deriving Inhabited

namespace Rule'

instance : BEq (Rule' α τ) where
  beq r s := r.name == s.name

instance [Ord α] : Ord (Rule' α τ) :=
  Ord.lexicographic
    ⟨λ r s => compare r.extra s.extra⟩
    ⟨λ r s => r.name.quickCmp s.name⟩

instance [Ord α] : LT (Rule' α τ) :=
  ltOfOrd

instance [Ord α] : LE (Rule' α τ) :=
  leOfOrd

@[inline]
def map (f : α → β) (g : τ → ι) (r : Rule' α τ) : Rule' β ι :=
  { r with tac := g r.tac, extra := f r.extra }

@[inline]
def mapExtra (f : α → β) (r : Rule' α τ) : Rule' β τ :=
  map f id r

@[inline]
def mapTac (f : τ → ι) (r : Rule' α τ) : Rule' α ι :=
  map id f r

@[inline]
def mapM [Monad m] (f : α → m β) (g : τ → m ι) (r : Rule' α τ) : m (Rule' β ι) :=
  return { r with tac := (← g r.tac), extra := (← f r.extra) }

@[inline]
def mapExtraM [Monad m] (f : α → m β) (r : Rule' α τ) : m (Rule' β τ) :=
  mapM f pure r

@[inline]
def mapTacM [Monad m] (f : τ → m ι) (r : Rule' α τ) : m (Rule' α ι) :=
  mapM pure f r

def tacToDescr (r : Rule' α SerializableRuleTac) :
    Rule' α (Option RuleTacDescr) :=
  r.mapTac (·.descr)

def descrToTac (r : Rule' α RuleTacDescr) : MetaM (Rule' α SerializableRuleTac) :=
  return { r with tac := (← r.tac.toRuleTac) }

end Rule'


/-! ### Normalisation Rules -/

structure NormRuleInfo where
  penalty : Int
  deriving Inhabited, DecidableEq

instance : Ord NormRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT NormRuleInfo :=
  ltOfOrd

instance : LE NormRuleInfo :=
  leOfOrd

abbrev NormRule' := Rule' NormRuleInfo
abbrev NormRule := NormRule' SerializableRuleTac

instance : ToFormat (NormRule' τ) where
  format r := f!"[{r.extra.penalty}] {r.name}"

def defaultNormPenalty : Int := 1


/-! ### Safe and Almost Safe Rules -/

inductive Safety
  | safe
  | almostSafe
  deriving Inhabited, DecidableEq

namespace Safety

instance : ToFormat Safety where
  format
    | safe => "safe"
    | almostSafe => "almostSafe"

end Safety

structure SafeRuleInfo where
  penalty : Int
  safety : Safety
  deriving Inhabited, DecidableEq

instance : Ord SafeRuleInfo where
  compare i j := compare i.penalty j.penalty

instance : LT SafeRuleInfo :=
  ltOfOrd

instance : LE SafeRuleInfo :=
  leOfOrd

abbrev SafeRule' := Rule' SafeRuleInfo
abbrev SafeRule := SafeRule' SerializableRuleTac

instance : ToFormat (SafeRule' τ) where
  format r := f!"[{r.extra.penalty}/{r.extra.safety}] {r.name}"

def defaultSafePenalty : Int := 1


/-! ### Unsafe Rules -/

structure UnsafeRuleInfo where
  successProbability : Percent
  deriving Inhabited

instance : Ord UnsafeRuleInfo where
  compare i j := compare j.successProbability i.successProbability
  -- NOTE: Rule with greater success probabilities are considered smaller.
  -- This is because we take 'small' to mean 'high priority'.

instance : LT UnsafeRuleInfo :=
  ltOfOrd

instance : LE UnsafeRuleInfo :=
  leOfOrd

abbrev UnsafeRule' := Rule' UnsafeRuleInfo
abbrev UnsafeRule := UnsafeRule' SerializableRuleTac

instance : ToFormat (UnsafeRule' τ) where
  format r := f!"[{r.extra.successProbability.toHumanString}] {r.name}"


/-! ### Regular Rules -/

inductive RegularRule' τ
  | safe (r : SafeRule' τ)
  | «unsafe» (r : UnsafeRule' τ)
  deriving BEq

abbrev RegularRule := RegularRule' SerializableRuleTac

instance [Inhabited τ] : Inhabited (RegularRule' τ) where
  default := RegularRule'.«safe» arbitrary

namespace RegularRule'

instance : ToFormat (RegularRule' τ) where
  format
    | (safe r) => format r
    | («unsafe» r) => format r

def successProbability : RegularRule' τ → Percent
  | (safe r) => Percent.hundred
  | («unsafe» r) => r.extra.successProbability

def isSafe : RegularRule' τ → Bool
  | (safe _) => true
  | («unsafe» _) => false

def isUnsafe : RegularRule' τ → Bool
  | (safe _) => false
  | («unsafe» _) => true

def tac : RegularRule' τ → τ
  | (safe r) => r.tac
  | («unsafe» r) => r.tac

def name : RegularRule' τ → Name
  | (safe r) => r.name
  | («unsafe» r) => r.name

end RegularRule'


/-! ## Rule Indices -/

structure RuleIndex (α : Type) where
  byTarget : DiscrTree α
  byHyp : DiscrTree α
  unindexed : Array α
  deriving Inhabited

namespace RuleIndex

open MessageData in
instance [ToMessageData α] : ToMessageData (RuleIndex α) where
  toMessageData ri := node #[
    "indexed by target:" ++ node (ri.byTarget.values.map toMessageData),
    "unindexed:" ++ node (ri.unindexed.map toMessageData)
    ]

def empty : RuleIndex α where
  byTarget := DiscrTree.empty
  byHyp := DiscrTree.empty
  unindexed := #[] -- TODO keep these sorted?

instance : EmptyCollection (RuleIndex α) :=
  ⟨empty⟩

@[specialize]
def add [BEq α] (r : α) (imode : IndexingMode) (ri : RuleIndex α) :
    RuleIndex α :=
  match imode with
  | IndexingMode.unindexed => { ri with unindexed := ri.unindexed.push r }
  | IndexingMode.target keys =>
    { ri with byTarget := ri.byTarget.insertCore keys r }
  | IndexingMode.hyps keys =>
    { ri with byHyp := ri.byHyp.insertCore keys r }

@[specialize]
def applicableByTargetRules (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (α × Array IndexMatchLocation)) := do
  let rs ← ri.byTarget.getMatch (← getMVarType goal)
  return rs.map λ r => (r, #[IndexMatchLocation.target])

@[specialize]
def applicableByHypRules (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (Array (α × Array IndexMatchLocation))) :=
  withMVarContext goal do
    let mut rulesList := #[]
    for localDecl in ← getLCtx do
      if localDecl.isAuxDecl then continue
      let rules ← ri.byHyp.getMatch localDecl.type
      let rules := rules.map λ r => (r, #[IndexMatchLocation.hyp localDecl])
      rulesList := rulesList.push rules
    return rulesList

-- TODO remove Inhabited as soon as qsort doesn't require it any more.
@[specialize]
def applicableRules [Ord α] (ri : RuleIndex α) (goal : MVarId) :
    MetaM (Array (α × Array IndexMatchLocation)) := do
  instantiateMVarDeclMVars goal
  let byTarget ← applicableByTargetRules ri goal
  let unindexed := ri.unindexed.map λ r => (r, #[IndexMatchLocation.none])
  let byHyp ← applicableByHypRules ri goal
  let result := mkRBMap _ _ compare
    |>.insertArrayWith byTarget combineLocations
    |>.insertArrayWith unindexed combineLocations
  let result := byHyp.foldl (init := result) λ result rs =>
    result.insertArrayWith rs combineLocations
  return result.toList.toArray
  where
    combineLocations (_ : α) (ls₁ ls₂ : Array IndexMatchLocation) :=
      ls₁ ++ ls₂

end RuleIndex


/-! ## Rule Set Members -/

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


/-! ## Rule Set -/

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
  MetaM (Array (NormRule × Array IndexMatchLocation)) :=
  rs.normRules.applicableRules goal

def applicableUnsafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array (UnsafeRule × Array IndexMatchLocation)) :=
  rs.unsafeRules.applicableRules goal

def applicableSafeRules (rs : RuleSet) (goal : MVarId) :
  MetaM (Array (SafeRule × Array IndexMatchLocation)) :=
  rs.safeRules.applicableRules goal

end RuleSet

end Aesop
