/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Constants
import Aesop.Rule

open Lean

namespace Aesop

structure PostponedSafeRule where
  rule : SafeRule
  output : RuleTacOutput
  deriving Inhabited

namespace PostponedSafeRule

def toUnsafeRule (r : PostponedSafeRule) : UnsafeRule :=
  { r.rule with extra := ⟨postponedSafeRuleSuccessProbability⟩ }

end PostponedSafeRule


inductive UnsafeQueueEntry
  | unsafeRule (r : IndexMatchResult UnsafeRule)
  | postponedSafeRule (r : PostponedSafeRule)
  deriving Inhabited

namespace UnsafeQueueEntry

instance : ToString UnsafeQueueEntry where
  toString
    | unsafeRule        r => toString r.rule.name
    | postponedSafeRule r => toString r.rule.name

def successProbability : UnsafeQueueEntry → Percent
  | unsafeRule r => r.rule.extra.successProbability
  | postponedSafeRule .. => postponedSafeRuleSuccessProbability

def name : UnsafeQueueEntry → RuleName
  | unsafeRule r => r.rule.name
  | postponedSafeRule r => r.rule.name

instance : Ord UnsafeQueueEntry :=
  ⟨ compareLexicographic
      (compareOpposite $ compareBy successProbability)
      (compareBy name) ⟩

end UnsafeQueueEntry


def UnsafeQueue := Subarray UnsafeQueueEntry

namespace UnsafeQueue

instance : EmptyCollection UnsafeQueue :=
  inferInstanceAs $ EmptyCollection (Subarray _)

instance : Inhabited UnsafeQueue :=
  inferInstanceAs $ Inhabited (Subarray _)

-- Precondition: `unsafeRules` is ordered lexicographically by descending
-- success probability, then by rule name.
def initial (postponedSafeRules : Array PostponedSafeRule)
    (unsafeRules : Array (IndexMatchResult UnsafeRule)) : UnsafeQueue :=
  let unsafeRules := unsafeRules.map .unsafeRule
  let postponedSafeRules :=
    postponedSafeRules.map .postponedSafeRule
      |>.qsort (λ x y => compare x y |>.isLT)
  postponedSafeRules.mergeSortedFilteringDuplicates unsafeRules |>.toSubarray

def entriesToMessageData (q : UnsafeQueue) : Array MessageData :=
  q.toArray.map toMessageData

end UnsafeQueue

end Aesop
