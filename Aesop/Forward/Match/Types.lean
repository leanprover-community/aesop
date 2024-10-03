import Aesop.Forward.PremiseIndex
import Aesop.Forward.SlotIndex
import Lean

set_option linter.missingDocs true

namespace Aesop

open Lean

/-- A substitution maps premise indices to assignments. -/
abbrev Substitution := AssocList PremiseIndex Expr

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
  ⟨{ revHyps := [default], subst := ∅ }⟩

set_option linter.missingDocs false in
/-- A complete match contains complete matches for each slot cluster. This means
there is one match for each slot cluster and each such match contains a
hypothesis for each of the slots. -/
structure CompleteMatch where
  clusterMatches : Array Match
  deriving Inhabited

end Aesop
