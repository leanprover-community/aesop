import Aesop.Rule.Name
import Aesop.Forward.PremiseIndex

set_option linter.missingDocs true

open Lean
open Std (HashMap)

namespace Aesop

set_option linter.missingDocs false in
/-- A cache for forward rule selection. -/
structure ForwardRuleCache where
  map : HashMap Expr (Array (RuleName × PremiseIndex))
  deriving Inhabited

instance : EmptyCollection ForwardRuleCache :=
  ⟨⟨∅⟩⟩

end Aesop
