import Aesop.Tree.RunMetaM
import Aesop.Tracing

open Lean
open MessageData

namespace Aesop

private def toYesNo : Bool → String
  | true => "yes"
  | false => "no"

protected def Goal.toMessageData (traceMods : TraceModifiers) (g : Goal) :
    MetaM MessageData := do
  match g.postNormGoalAndState? with
  | some (_, postNormMetaState) =>
    postNormMetaState.runMetaM' (addMessageContext (← go))
  | none =>
    (← g.parentMetaState).runMetaM' (addMessageContext (← go))
  where
    go : MetaM MessageData := do
      let unsafeQueueLength :=
        if ¬ g.unsafeRulesSelected
          then f!"<not selected>"
          else format g.unsafeQueue.size
      let originalGoalId :=
        match g.originalGoalId? with
        | none => "<none>"
        | some gid => toString gid
      let postNormGoal :=
        match g.postNormGoal? with
        | none => "<none>"
        | some m => toString m.name
      return m!"Goal {g.id} [{g.priority.toHumanString} / {g.successProbability.toHumanString}]" ++ nodeFiltering #[
        m!"Unsafe rules in queue: {unsafeQueueLength}, failed: {g.failedRapps.size}",
        m!"state: {g.state} | irrelevant: {toYesNo g.isIrrelevant} | normal: {toYesNo g.isNormal} | depth: {g.depth}",
        m!"Iteration added: {g.addedInIteration} | last expanded: {g.lastExpandedInIteration} | copy of goal: {originalGoalId}",
        -- TODO hide mvar info (at least by default)
        m!"Pre-norm goal mvar: {g.preNormGoal.name} | Post-norm goal mvar: {postNormGoal}",
        m!"Unassigned mvars: {g.mvars.map (·.name)}",
        if ! traceMods.goals then none else
          m!"Goal:{indentD $ ofGoal g.currentGoal}",
        if ! traceMods.unsafeQueues || ! g.unsafeRulesSelected then none else
          m!"Unsafe queue:{node g.unsafeQueue.entriesToMessageData}",
        if ! traceMods.failedRapps then none else
          m!"Failed rule applications:{node $ g.failedRapps.map toMessageData}"
      ]

protected def Rapp.toMessageData (traceMods : TraceModifiers) (r : Rapp) :
    MetaM MessageData := do
  Prod.fst <$> r.runMetaM (addMessageContext (← go))
  where
    go : MetaM MessageData := do
      let mvarClusters ← r.children.mapM λ cref => do
        (← cref.get).goals.mapM λ gref => return (← gref.get).id
      return m!"Rapp {r.id} [{r.successProbability.toHumanString}]" ++
        nodeFiltering #[
          toMessageData r.appliedRule,
          m!"state: {r.state} | irrelevant: {toYesNo r.isIrrelevant}",
          -- TODO hide mvars by default
          m!"introduced mvars: {r.introducedMVars.map (·.name)}",
          m!"assigned mvars: {r.assignedMVars.map (·.name)}",
          m!"mvar clusters: {mvarClusters}"
        ]

private def nodeMessageSeparator : String :=
  "-*-*-*-*-*-\n"

mutual
  private partial def goalTreeToMessageData (traceMods : TraceModifiers)
      (goal : Goal) : MetaM MessageData := do
    let goalMsg ← goal.toMessageData traceMods
    let childrenMsgs ← goal.children.mapM λ c => do
      rappTreeToMessageData traceMods (← c.get)
    return nodeMessageSeparator ++ goalMsg ++ MessageData.node childrenMsgs

  private partial def rappTreeToMessageData (traceMods : TraceModifiers)
      (rapp : Rapp) : MetaM MessageData := do
    let rappMsg ← rapp.toMessageData traceMods
    let childrenMsgs ←
      rapp.children.concatMapM λ cref => do
        (← cref.get).goals.mapM λ gref => do
          goalTreeToMessageData traceMods (← gref.get)
    return nodeMessageSeparator ++ rappMsg ++ MessageData.node childrenMsgs
end

def Goal.treeToMessageData (traceMods : TraceModifiers) (g : Goal) :
    MetaM MessageData :=
  goalTreeToMessageData traceMods g

def Rapp.treeToMessageData (traceMods : TraceModifiers) (r : Rapp) :
    MetaM MessageData := do
  rappTreeToMessageData traceMods r

end Aesop
