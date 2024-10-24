import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Aesop.Forward.Substitution
import Aesop.Rule.Forward
import Lean

set_option linter.missingDocs true

namespace Aesop

open Lean

/-- A match associates hypotheses to (a prefix of) the slots of a slot
cluster. -/
structure Match where
  /-- Hyps for each slot, in reverse order. If there are `n` slots, the `i`th
  hyp in `revHyps` is the hyp associated with the slot with index `n - i`. -/
  revHyps : List FVarId
  /-- `revHyps` is nonempty --/
  revHyps_ne : 0 < revHyps.length := by simp
  /-- The substitution induced by the assignment of the hyps in `hyps` to the
  rule's slots. -/
  subst : Substitution

instance : Inhabited Match :=
  ⟨{ revHyps := [default], subst := default }⟩

instance : BEq Match where
  beq m₁ m₂ := m₁.revHyps == m₂.revHyps

instance : Hashable Match where
  hash m := hash m.revHyps

instance : ToMessageData Match where
  toMessageData m := toMessageData $ m.revHyps.reverse.map Expr.fvar

set_option linter.missingDocs false in
/-- A complete match contains complete matches for each slot cluster. This means
there is one match for each slot cluster and each such match contains a
hypothesis for each of the slots. -/
structure CompleteMatch where
  clusterMatches : Array Match
  deriving Inhabited, BEq, Hashable

-- TODO hash as a computed field

/-- An entry in the forward state queues. Represents a complete match. -/
structure ForwardRuleMatch where
  /-- The rule to which this match belongs. -/
  rule : ForwardRule
  /-- The match. -/
  «match» : CompleteMatch
  deriving Inhabited, BEq, Hashable

end Aesop
