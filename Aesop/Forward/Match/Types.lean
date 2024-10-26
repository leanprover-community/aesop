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
  revElems : List MatchElem
  /-- The substitution induced by the assignment of the hyps in `hyps` to the
  rule's slots (or, for rule pattern slots, by the pattern instantiation). -/
  subst : Substitution
  /-- The match's level is the maximal slot index that has a corresponding
  element in `revElems`. -/
  level : SlotIndex
  deriving Inhabited

instance : BEq Match where
  beq m₁ m₂ := m₁.revElems == m₂.revElems

instance : Hashable Match where
  hash m := hash m.revElems

instance : ToMessageData Match where
  toMessageData m := toMessageData $
    m.revElems.reverse.map λ
      | .hyp fvarId => m!"{Expr.fvar fvarId}"
      | .patInst subst => m!"<pattern inst {subst}>"

set_option linter.missingDocs false in
/-- A complete match contains complete matches for each slot cluster. This means
there is one match for each slot cluster and each such match contains a
hypothesis for each of the slots. -/
structure CompleteMatch where
  clusterMatches : Array Match
  deriving Inhabited, BEq, Hashable

instance : ToMessageData CompleteMatch where
  toMessageData m := toMessageData m.clusterMatches

-- TODO hash as a computed field

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardRuleMatch where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : CompleteMatch
  deriving Inhabited, BEq, Hashable

instance : ToMessageData ForwardRuleMatch where
  toMessageData m := m!"{m.rule} {m.match}"

end Aesop
