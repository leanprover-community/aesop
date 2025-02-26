import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Forward.Substitution
import Aesop.Rule.Forward

set_option linter.missingDocs true

namespace Aesop

open Lean

/-- A match associates hypotheses to (a prefix of) the slots of a slot
cluster. -/
structure Match where
  /-- The substitution induced by the hyps or pattern substitutions added to
  the slots. -/
  subst : Substitution
  /-- The pattern substitutions that have been added to the match. -/
  patInstSubsts : Array Substitution
  /-- The match's level is the index of the maximal slot for which a hyp or
  pattern substitution has been added to the match. -/
  level : SlotIndex
  /-- Premises that appear in slots which are as yet unassigned in this match
  (i.e., in slots with index greater than `level`). This is a property of the
  rule, but we include it here because it's used to check whether two matches
  are equivalent. -/
  forwardDeps : Array PremiseIndex
  /-- Premises that appear in the rule's conclusion. This is a property of the
  rule, but we include it here because it's used to check whether two matches
  are equivalent. -/
  conclusionDeps : Array PremiseIndex
  deriving Inhabited

namespace Match

/-- Two matches are equivalent if (a) they have the same level; (b) for each
premise that appears in a slot greater than the matches' level, their
substitution assigns the same value; (c) for each premise that appears in the
rule's conclusion, their substitution assigns the same value.

If we already have a match `m₁` and we obtain an equivalent match `m₂`, then
`m₂` is redundant. This is because if the matches are partial, then `m₂` can be
completed by exactly the hypotheses that complete `m₁`, since they agree on the
premise instantiations that are relevant for the possible completions. And if
the matches are complete, then they assign the same instantiations to the
variables that appear in the rule's conclusion, and these are the only ones that
ultimately matter. -/
-- TODO I believe we could be even more aggressive when forwardDeps and
-- conclusionDeps contain proofs of propositions and consider any such proofs
-- equal.
protected def equiv (m₁ m₂ : Match) : Bool :=
  m₁.level == m₂.level &&
  m₁.forwardDeps.all    (λ p => m₁.subst.find? p == m₂.subst.find? p) &&
  m₁.conclusionDeps.all (λ p => m₁.subst.find? p == m₂.subst.find? p)

instance : BEq Match :=
  ⟨Match.equiv⟩

instance : Hashable Match where
  hash m :=
    let h := hash m.level
    let h :=
      m.forwardDeps.foldl  (init := h) λ h p => mixHash h $ hash (m.subst.find? p)
    m.conclusionDeps.foldl (init := h) λ h p => mixHash h $ hash (m.subst.find? p)

instance : Ord Match where
  compare m₁ m₂ :=
    compare m₁.level m₂.level |>.then $
    if m₁ == m₂ then .eq else
    compare m₁.subst m₂.subst

instance : ToMessageData Match where
  toMessageData m := m!"{m.subst}"

end Match

set_option linter.missingDocs false in
/-- A complete match contains complete matches for each slot cluster. This means
there is one match for each slot cluster and each such match contains a
hypothesis for each of the slots. -/
structure CompleteMatch where
  clusterMatches : Array Match
  deriving Inhabited, BEq, Hashable

-- TODO hash as a computed field

instance : EmptyCollection CompleteMatch :=
  ⟨{ clusterMatches := ∅ }⟩

instance : Ord CompleteMatch where
  compare m₁ m₂ :=
    compareArraySizeThenLex compare m₁.clusterMatches m₂.clusterMatches

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardRuleMatch where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : CompleteMatch
  deriving Inhabited, BEq, Hashable

namespace ForwardRuleMatch

/-- Compare two queue entries by rule priority, rule name and the expressions
contained in the match. Higher-priority rules are considered less (since the
queues are min-queues). The ordering on expressions is arbitrary. -/
protected instance ord : Ord ForwardRuleMatch where
  compare m₁ m₂ :=
    compare m₁.rule m₂.rule |>.then $
    compare m₁.match m₂.match

@[inherit_doc ForwardRuleMatch.ord]
protected def le (m₁ m₂ : ForwardRuleMatch) : Bool :=
  compare m₁ m₂ |>.isLE

end Aesop.ForwardRuleMatch
