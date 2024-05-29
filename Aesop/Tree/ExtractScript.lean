/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tracing
import Aesop.Tree.TreeM

open Lean
open Lean.Meta
open Lean.Parser.Tactic (tacticSeq)

namespace Aesop

abbrev ExtractScriptM := StateRefT UnstructuredScript TreeM

def visitGoal (g : Goal) : ExtractScriptM (Option (MVarId × Meta.SavedState)) := do
  match g.normalizationState with
  | .notNormal => throwError "expected goal {g.id} to be normalised"
  | .provenByNormalization _ normScript? =>
    go g.id normScript?
    return none
  | .normal postGoal postState normScript? =>
    go g.id normScript?
    return some (postGoal, postState)
where
  go (gid : GoalId) : Except DisplayRuleName UnstructuredScript →
      ExtractScriptM Unit
    | .ok script => do
      modify (· ++ script)
    | .error rule => throwError "normalization rule {rule} (at goal {gid}) does not support tactic script generation"

def visitRapp (r : Rapp) (preGoal : MVarId) (preState : Meta.SavedState) :
    ExtractScriptM Unit := do
  let postState := r.metaState
  let (some scriptBuilder) := r.scriptBuilder?
    | throwError "rule {r.appliedRule.name} (at rapp {r.id}) does not support tactic script generation"
  let tacticSeq ←
    try
      postState.runMetaM' scriptBuilder.unstructured.run
    catch e =>
      throwError "script builder for rapp {r.id} reported error:{indentD $ e.toMessageData}"
  let postGoals ← postState.runMetaM' do
    r.originalSubgoals.mapM λ g => return ⟨g, ← g.getMVarDependencies⟩
  modify λ s => s.push { postState, tacticSeq, preGoal, postGoals, preState }

mutual
  partial def MVarClusterRef.extractScriptCore (cref : MVarClusterRef) :
      ExtractScriptM Unit := do
    let c ← cref.get
    let (some gref) ← c.provenGoal? | throwError
      m!"the mvar cluster with goals {(← c.goals.mapM (·.get)).map (·.id)} does not contain a proven goal"
    gref.extractScriptCore

  partial def GoalRef.extractScriptCore (gref : GoalRef) : ExtractScriptM Unit := do
    let g ← gref.get
    if let some (postNormGoal, postNormState) ← visitGoal g then
      let (some rref) ← g.firstProvenRapp? | throwError
        m!"goal {g.id} does not have a proven rapp"
      rref.extractScriptCore postNormGoal postNormState

  partial def RappRef.extractScriptCore (rref : RappRef) (preGoal : MVarId)
      (preState : Meta.SavedState) : ExtractScriptM Unit := do
    let r ← rref.get
    visitRapp r preGoal preState
    r.children.forM (·.extractScriptCore)
end

@[inline]
def extractScript : TreeM UnstructuredScript := do
  (·.snd) <$> (← getRootGoal).extractScriptCore.run #[]

mutual
  partial def MVarClusterRef.extractSafePrefixScriptCore
      (mref : MVarClusterRef) : ExtractScriptM Unit := do
    (← mref.get).goals.forM (·.extractSafePrefixScriptCore)

  partial def GoalRef.extractSafePrefixScriptCore (gref : GoalRef) :
      ExtractScriptM Unit := do
    let g ← gref.get
    if let some (postNormGoal, postNormState) ← visitGoal g then
      let safeRapps ← g.safeRapps
      if safeRapps.size > 1 then
        throwError "aesop: internal error: goal {g.id} has {safeRapps.size} safe rapps"
      if let some rref := safeRapps[0]? then
        rref.extractSafePrefixScriptCore postNormGoal postNormState

  partial def RappRef.extractSafePrefixScriptCore (rref : RappRef)
      (preGoal : MVarId) (preState : Meta.SavedState) :
      ExtractScriptM Unit := do
    let r ← rref.get
    visitRapp r preGoal preState
    r.forSubgoalsM (·.extractSafePrefixScriptCore)
end

def extractSafePrefixScript : TreeM UnstructuredScript := do
  (·.snd) <$> (← getRootGoal).extractSafePrefixScriptCore.run #[]

end Aesop
