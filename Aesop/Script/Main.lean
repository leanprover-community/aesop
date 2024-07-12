/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Options
import Aesop.Script.Check
import Aesop.Script.StructureDynamic
import Aesop.Script.StructureStatic
import Aesop.Script.OptimizeSyntax

open Lean
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop.Script

def UScript.optimize (uscript : UScript)  (preState : Meta.SavedState)
    (goal : MVarId) : MetaM (Option (TSyntax ``tacticSeq × Bool)) := do
  let structureResult? ←
    if aesop.dev.dynamicStructuring.get (← getOptions) then
      uscript.toSScriptDynamic preState goal
    else
      let tacticState ← preState.runMetaM' $ TacticState.mkInitial goal
      uscript.toSScriptStatic tacticState
  let some (sscript, perfect) := structureResult?
    | return none
  let tacticSeq ← `(tacticSeq| $(← sscript.render):tactic*)
  let tacticSeq ← optimizeSyntax tacticSeq
  return (tacticSeq, perfect)

end Script

open Script

def checkAndTraceScript (uscript : UScript)
    (sscript? : Option (TSyntax ``tacticSeq)) (preState : Meta.SavedState)
    (goal : MVarId) (options : Aesop.Options') (expectCompleteProof : Bool)
    (tacticName : String) :
    MetaM Unit := do
  if let some script := sscript? then
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
    else
      logWarning m!"{tacticName}: structuring the script failed. Reporting unstructured script."

end Aesop
