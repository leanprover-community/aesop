/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.Check
import Aesop.Script.StructureDynamic
import Aesop.Script.StructureStatic
import Aesop.Script.OptimizeSyntax
import Aesop.Stats.Basic
import Aesop.Options.Internal

open Lean
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop.Script

def UScript.optimize (uscript : UScript) (proofHasMVar : Bool)
    (preState : Meta.SavedState) (goal : MVarId) :
    MetaM (Option (TSyntax ``tacticSeq × ScriptGenerated)) := do
  let structureResult? ← do
    let opts ← getOptions
    if aesop.dev.dynamicStructuring.get opts &&
       ! (aesop.dev.optimizedDynamicStructuring.get opts && ! proofHasMVar) then
      structureDynamic
    else
      structureStatic
  let some (sscript, gen) := structureResult?
    | return none
  let tacticSeq ← `(tacticSeq| $(← sscript.render):tactic*)
  let tacticSeq ← optimizeSyntax tacticSeq
  return some (tacticSeq, gen)
where
  structureStatic : MetaM (Option (SScript × ScriptGenerated)) := do
    let tacticState ← preState.runMetaM' $ TacticState.mkInitial goal
    let (sscript, perfect) ← uscript.toSScriptStatic tacticState
    let gen :=
      .staticallyStructured (perfect := perfect) (hasMVar := proofHasMVar)
    pure $ some (sscript, gen)

  structureDynamic : MetaM (Option (SScript × ScriptGenerated)) := do
    let some (script, perfect) ← uscript.toSScriptDynamic preState goal
      | return none
    let gen :=
      .dynamicallyStructured (perfect := perfect) (hasMVar := proofHasMVar)
    return some (script, gen)

end Script

open Script

variable [Monad m] [MonadLog m] [MonadRef m] [MonadError m] [AddMessageContext m]
  [MonadStats m] [MonadLiftT MetaM m] in
def checkAndTraceScript (uscript : UScript)
    (sscript? : Option (TSyntax ``tacticSeq × ScriptGenerated)) (preState : Meta.SavedState)
    (goal : MVarId) (options : Aesop.Options') (expectCompleteProof : Bool)
    (tacticName : String) :
    m Unit := do
  if let some (script, scriptGenerated) := sscript? then
    recordScriptGenerated scriptGenerated
    if options.traceScript then
      addTryThisTacticSeqSuggestion (← getRef) script
    checkRenderedScriptIfEnabled script preState goal
      (expectCompleteProof := expectCompleteProof)
  else
    if options.traceScript then
      let tacticSeq ← uscript.renderTacticSeq preState goal
      addTryThisTacticSeqSuggestion (← getRef) tacticSeq
    if ← Check.script.isEnabled then
      throwError "{Check.script.name}: structuring the script failed"
    else if options.traceScript then
      logWarning m!"{tacticName}: structuring the script failed. Reporting unstructured script."

end Aesop
