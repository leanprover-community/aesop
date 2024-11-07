import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Forward.Substitution
import Aesop.Rule.Forward

set_option linter.missingDocs true

namespace Aesop

open Lean

/-- An element of a match. This is either a hypothesis or a pattern
instantiation. -/
inductive MatchElem
  /-- A hypothesis. -/
  | hyp (fvarId : FVarId)
  /-- A pattern instantiation with the given substitution. -/
  | patInst (subst : Substitution)
  deriving Inhabited, Hashable, BEq

namespace MatchElem

instance : ToMessageData MatchElem where
  toMessageData
    | .hyp fvarId => m!"{Expr.fvar fvarId}"
    | .patInst subst => m!"<pat inst {subst}>"

/-- Create a match element for a hyp or pattern substitution. -/
def ofHypAndSubst (hyp? : Option FVarId) (subst : Substitution) : MatchElem :=
  match hyp? with
  | none => .patInst subst
  | some fvarId => .hyp fvarId

end MatchElem

/-- A match associates hypotheses to (a prefix of) the slots of a slot
cluster. -/
structure Match where
  /-- Hyps or pattern instantiations for each slot, in reverse order.
  If there are `n` slots, the `i`th element in `revHyps` is the hyp or pattern
  instantiation associated with the slot with index `n - i`. -/
  -- TODO why do we even collect these? Isn't the substitution enough?
  revElems : List MatchElem
  /-- The substitution induced by the assignment of the hyps in `hyps` to the
  rule's slots (or, for rule pattern slots, by the pattern instantiation). -/
  subst : Substitution
  /-- The match's level is the maximal slot index that has a corresponding
  element in `revElems`. -/
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

instance : ToMessageData Match where
  toMessageData m := toMessageData $
    m.revElems.reverse.map λ
      | .hyp fvarId => m!"{Expr.fvar fvarId}"
      | .patInst subst => m!"<pattern inst {subst}>"

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

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardRuleMatch where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : CompleteMatch
  deriving Inhabited, BEq, Hashable

end Aesop
