import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

structure NeuralBuilderOptions extends RegularBuilderOptions where
  /-- The transparency used by the rule tactic. -/
  transparency : TransparencyMode
  /-- The transparency used to index the rule. The rule is not indexed unless
  this is `.reducible`. -/
  indexTransparency : TransparencyMode
  neuralProver : String
  numReturnSequences : UInt64
  maxLength : UInt64
  temperature : Float
  numBeams : UInt64


instance : Inhabited NeuralBuilderOptions where
  default := {
    toRegularBuilderOptions := default
    transparency := .default
    indexTransparency := .reducible
    neuralProver := "onnx-leandojo-lean4-tacgen-byt5-small"
    numReturnSequences := 32
    maxLength := 256
    temperature := 1.0
    numBeams := 1
  }

def RuleBuilder.neural (opts : NeuralBuilderOptions) : RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global _ => do
    -- let tac := .neuralProvers opts.neuralProver opts.numReturnSequences
    --     opts.maxLength opts.temperature opts.numBeams
    let tac := .neuralProvers opts.neuralProver
    -- let type := (← getConstInfo decl).type
    RuleBuilderOutput.global <$> mkResult tac
  | RuleBuilderKind.local _ _ =>
    throwError "neural rule builder does not support local hypotheses"
    -- goal.withContext do
    --   let tac := RuleTacDescr.applyFVar fvarUserName opts.transparency
    --   let type ← instantiateMVars (← getLocalDeclFromUserName fvarUserName).type
    --   let result ← mkResult tac
    --   return RuleBuilderOutput.local goal result
  where
    mkResult (tac : RuleTacDescr) : MetaM RuleBuilderResult :=
      return RuleBuilderResult.regular {
        builder := BuilderName.neural
        tac := tac
        -- indexingMode := ← opts.getIndexingModeM do
        --   if opts.indexTransparency != .reducible then
        --     return .unindexed
        --   else
        --     IndexingMode.targetMatchingConclusion type
        indexingMode := ← opts.getIndexingModeM $ pure IndexingMode.unindexed
      }

end Aesop
