/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Script.UScript
import Aesop.Tracing
import Aesop.Tree.TreeM

open Lean
open Lean.Meta
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop

open Script

structure ExtractScriptM.State where
  script : UScript := #[]
  proofHasMVar : Bool := false

abbrev ExtractScriptM := StateRefT ExtractScriptM.State TreeM

def ExtractScriptM.run (x : ExtractScriptM α) : TreeM (UScript × Bool) := do
  let (_, r) ← StateRefT'.run x {}
  return (r.script, r.proofHasMVar)

namespace ExtractScript

def lazyStepToStep (ruleName : DisplayRuleName) (lstep : LazyStep) :
    MetaM Step :=
  try
    lstep.toStep
  catch e =>
    throwError "tactic script generation failed for rule {ruleName}:{indentD e.toMessageData}"

def lazyStepsToSteps (ruleName : DisplayRuleName) :
    Option (Array LazyStep) → MetaM (Array Step)
  | none => throwError "tactic script generation is not supported by rule {ruleName}"
  | some lsteps => lsteps.mapM (lazyStepToStep ruleName)

def recordStep (step : Script.Step) : ExtractScriptM Unit := do
  modify λ s => { s with script := s.script.push step }

def recordLazySteps (ruleName : DisplayRuleName)
    (steps? : Option (Array Script.LazyStep)) : ExtractScriptM Unit := do
  let steps ← lazyStepsToSteps ruleName steps?
  modify λ s => { s with script := s.script ++ steps }

def visitGoal (g : Goal) : ExtractScriptM Unit := do
  withConstAesopTraceNode .script (return m!"goal {g.id}") do
  if ! g.mvars.isEmpty then
    modify λ s => { s with proofHasMVar := true }
  match g.normalizationState with
  | .notNormal => throwError "expected goal {g.id} to be normalised"
  | .normal (script := script) ..
  | .provenByNormalization (script := script) .. =>
    for (ruleName, script?) in script do
      recordLazySteps ruleName script?

def visitRapp (r : Rapp) : ExtractScriptM Unit := do
  withConstAesopTraceNode .script (return m!"rapp {r.id}") do
  recordLazySteps r.appliedRule.name r.scriptSteps?

end ExtractScript

open ExtractScript

mutual
  partial def MVarClusterRef.extractScriptCore (cref : MVarClusterRef) :
      ExtractScriptM Unit := do
    let c ← cref.get
    let (some gref) ← c.provenGoal? | throwError
      m!"the mvar cluster with goals {(← c.goals.mapM (·.get)).map (·.id)} does not contain a proven goal"
    gref.extractScriptCore

  partial def GoalRef.extractScriptCore (gref : GoalRef) : ExtractScriptM Unit := do
    let g ← gref.get
    visitGoal g
    if ! g.normalizationState.isProvenByNormalization then
      let (some rref) ← g.firstProvenRapp? | throwError
        m!"goal {g.id} does not have a proven rapp"
      rref.extractScriptCore

  partial def RappRef.extractScriptCore (rref : RappRef) :
      ExtractScriptM Unit := do
    let r ← rref.get
    visitRapp r
    r.children.forM (·.extractScriptCore)
end

@[inline]
def extractScript : TreeM (UScript × Bool) :=
  withAesopTraceNode .script (λ r => return m!"{exceptEmoji r} Extract script") do
    (← getRootGoal).extractScriptCore.run

mutual
  partial def MVarClusterRef.extractSafePrefixScriptCore
      (mref : MVarClusterRef) : ExtractScriptM Unit := do
    (← mref.get).goals.forM (·.extractSafePrefixScriptCore)

  partial def GoalRef.extractSafePrefixScriptCore (gref : GoalRef) :
      ExtractScriptM Unit := do
    let g ← gref.get
    visitGoal g
    if ! g.normalizationState.isProvenByNormalization then
      let safeRapps ← g.safeRapps
      if safeRapps.size > 1 then
        throwError "aesop: internal error: goal {g.id} has {safeRapps.size} safe rapps"
      if let some rref := safeRapps[0]? then
        rref.extractSafePrefixScriptCore
      else
        let some (postNormGoal, postNormState) := g.postNormGoalAndMetaState?
          | throwError "aesop: internal error at extractSafePrefixScript: goal {g.id} is not normalised"
        recordStep $ ← Step.mkSorry postNormGoal postNormState

  partial def RappRef.extractSafePrefixScriptCore (rref : RappRef) :
      ExtractScriptM Unit := do
    let r ← rref.get
    visitRapp r
    -- The safe prefix can't assign mvars because any safe rule that assigns
    -- mvars is downgraded to an unsafe rule. So we add `sorry` steps for all
    -- introduced mvars.
    for mvarId in r.introducedMVars do
      recordStep $ ← Step.mkSorry mvarId r.metaState
    r.forSubgoalsM (·.extractSafePrefixScriptCore)
end

def extractSafePrefixScript : TreeM (UScript × Bool) := do
  withAesopTraceNode .script (λ r => return m!"{exceptEmoji r} Extract safe prefix script") do
    (← getRootGoal).extractSafePrefixScriptCore.run

end Aesop
