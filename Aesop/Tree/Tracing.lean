import Aesop.Tree.RunMetaM
import Aesop.Tracing

open Lean
open MessageData

namespace Aesop

private def toYesNo : Bool → String
  | true => "yes"
  | false => "no"

def Goal.withHeadlineTraceNode (g : Goal) (traceOpt : TraceOption) (k : MetaM α)
    (collapsed := true) (transform : MessageData → MetaM MessageData := pure) :
    MetaM α := do
  withConstAesopTraceNode traceOpt fmt k collapsed
  where
    fmt : MetaM MessageData := do
      g.runMetaMInParentState' do
        g.preNormGoal.withContext do
          addMessageContext $ ← transform
            m!"{g.state.toEmoji} G{g.id} [{g.priority.toHumanString}] ⋯ ⊢ {← g.preNormGoal.getType}"

def Goal.traceMetadata (g : Goal) (traceOpt : TraceOption) : MetaM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  trc m!"ID: {g.id}"
  trcNode m!"Pre-normalisation goal ({g.preNormGoal.name}):" do
    g.runMetaMInParentState' do
      trc m!"{g.preNormGoal}"
  match g.postNormGoalAndMetaState? with
  | none =>
    trc m!"Post-normalisation goal: <goal not normalised>"
  | some (goal, state) =>
    state.runMetaM' do
      trcNode m!"Post-normalisation goal ({goal.name}):" do
        trc m!"{goal}"
  trc m!"Metavariables: {g.mvars.toArray.map (·.name)}"
  trc m!"Parent rapp:  {← (← g.parentRapp?).mapM λ rref => (·.id) <$> rref.get}"
  trc m!"Child rapps:  {← g.children.mapM λ rref => (·.id) <$> rref.get}"
  trc m!"Origin: {g.origin.toString}" -- TODO
  trc m!"Depth: {g.depth}"
  trc m!"State: {g.state.toEmoji} {g.state}"
  trc m!"Irrelevant: {toYesNo g.isIrrelevant}"
  trc m!"Forced unprovable: {toYesNo g.isForcedUnprovable}"
  trc m!"Added in iteration: {g.addedInIteration}"
  trc m!"Last expanded in iteration: {if g.lastExpandedInIteration == .none then "never" else toString $ g.lastExpandedInIteration}"
  if g.unsafeRulesSelected then
    if g.unsafeQueue.isEmpty then
      trc m!"Unsafe rule queue: <empty>"
    else
      trcNode m!"Unsafe rule queue:" do
        for r in g.unsafeQueue.toArray do
          trc m!"[{r.successProbability.toHumanString}] {r.name}"
  else
    trc m!"Unsafe rule queue: <not selected>"
  if g.failedRapps.isEmpty then
    trc m!"Failed rules: <none>"
  else
    trcNode m!"Failed rules:" do
      for r in g.failedRapps do
        trc m!"[{r.successProbability.toHumanString}] {r.name}"
  where
    trc msg : MetaM Unit := do aesop_trace![traceOpt] msg

    trcNode msg (k : MetaM Unit) : MetaM Unit :=
      withConstAesopTraceNode traceOpt (return msg) k

def Rapp.withHeadlineTraceNode (r : Rapp) (traceOpt : TraceOption) (k : MetaM α)
    (collapsed := true) (transform : MessageData → MetaM MessageData := pure) :
    MetaM α :=
  withConstAesopTraceNode traceOpt
    (transform m!"{r.state.toEmoji} R{r.id} [{r.successProbability.toHumanString}] {r.appliedRule.name}")
    k collapsed

def Rapp.traceMetadata (r : Rapp) (traceOpt : TraceOption) : MetaM Unit := do
  if ! (← traceOpt.isEnabled) then
    return
  trc m!"ID: {r.id}"
  trc m!"Rule: {r.appliedRule}"
  trc m!"Success probability: {r.successProbability.toHumanString}"
  trc m!"Parent goal: {(← r.parent.get).id}"
  trc m!"Child goals: {← (← r.subgoals).mapM λ gref => (·.id) <$> gref.get}"
  trc m!"State: {r.state}"
  trc m!"Irrelevant: {r.isIrrelevant}"
  trc m!"Introduced metavariables: {r.introducedMVars.toArray.map (·.name)}"
  trc m!"Assigned   metavariables: {r.assignedMVars.toArray.map (·.name)}"
  where
    trc m : MetaM Unit := do aesop_trace![traceOpt] m

mutual
  partial def Goal.traceTreeCore (g : Goal) (traceOpt : TraceOption) :
      MetaM Unit :=
    g.withHeadlineTraceNode traceOpt (collapsed := false) do
      g.runMetaMInParentState' do
        aesop_trace![traceOpt] g.preNormGoal
      withConstAesopTraceNode traceOpt (return "Metadata") do
        g.traceMetadata traceOpt
      for rref in g.children do
        (← rref.get).traceTreeCore traceOpt

  partial def Rapp.traceTreeCore (r : Rapp) (traceOpt : TraceOption) :
      MetaM Unit := do
    r.withHeadlineTraceNode traceOpt (collapsed := false) do
      withConstAesopTraceNode traceOpt (return "Metadata") do
        r.traceMetadata traceOpt
      r.forSubgoalsM λ gref => do
        (← gref.get).traceTreeCore traceOpt
end

def Goal.traceTree (g : Goal) (traceOpt : TraceOption) : MetaM Unit := do
  if ← traceOpt.isEnabled then
    g.traceTreeCore traceOpt

def Rapp.traceTree (r : Rapp) (traceOpt : TraceOption) : MetaM Unit := do
  if ← traceOpt.isEnabled then
    r.traceTreeCore traceOpt

end Aesop
