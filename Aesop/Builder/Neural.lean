import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

def RuleBuilder.neural (opts : RegularBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global _ => do
    let tac := .neuralProvers
    RuleBuilderOutput.global <$> mkResult tac
  | RuleBuilderKind.local _ _ =>
    throwError "neural rule builder does not support local hypotheses"
  where
    mkResult (tac : RuleTacDescr) : MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.neural
        tac := tac
        indexingMode := ← opts.getIndexingModeM $ pure IndexingMode.unindexed
      }

end Aesop
