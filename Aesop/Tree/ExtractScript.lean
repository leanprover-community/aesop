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

abbrev ExtractScriptM := StateRefT UScript TreeM

private def lazyStepToStep (ruleName : DisplayRuleName) (lstep : LazyStep) :
    MetaM Step :=
  try
    lstep.toStep
  catch e =>
    throwError "tactic script generation failed for rule {ruleName}:{indentD e.toMessageData}"

private def lazyStepsToSteps (ruleName : DisplayRuleName) :
    Option (Array LazyStep) → MetaM (Array Step)
  | none => throwError "tactic script generation is not supported by rule {ruleName}"
  | some lsteps => lsteps.mapM (lazyStepToStep ruleName)

def visitGoal (g : Goal) : ExtractScriptM Unit := do
  match g.normalizationState with
  | .notNormal => throwError "expected goal {g.id} to be normalised"
  | .normal (script := script) ..
  | .provenByNormalization (script := script) .. =>
    for (rule, script?) in script do
      let script ← lazyStepsToSteps rule script?
      modify (· ++ script)

def visitRapp (r : Rapp) : ExtractScriptM Unit := do
  let lsteps? := r.scriptSteps?
  let steps ← lazyStepsToSteps r.appliedRule.name lsteps?
  modify λ s => s ++ steps

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
def extractScript : TreeM UScript := do
  (·.snd) <$> (← getRootGoal).extractScriptCore.run #[]

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

  partial def RappRef.extractSafePrefixScriptCore (rref : RappRef) :
      ExtractScriptM Unit := do
    let r ← rref.get
    visitRapp r
    r.forSubgoalsM (·.extractSafePrefixScriptCore)
end

def extractSafePrefixScript : TreeM UScript := do
  (·.snd) <$> (← getRootGoal).extractSafePrefixScriptCore.run #[]

end Aesop
