/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean

namespace Aesop

-- A TraceOption determines *whether* a certain piece of information is printed.
structure TraceOption where
  traceName : Name
  option : Lean.Option Bool
  parentOption : Option (Lean.Option Bool)
  deriving Inhabited

def registerTraceOption (traceName : Name) (defValue : Bool) (descr : String) :
    IO TraceOption := do
  let opt ←
    Option.register (`trace.aesop ++ traceName)
      { defValue := defValue, group := "trace", descr := descr }
  return {
    traceName := `aesop ++ traceName,
    option := opt,
    parentOption := none
  }

namespace TraceOption

initialize ruleSet : TraceOption ←
  registerTraceOption `ruleSet false
    "(aesop) Print the rule set before starting the search."

initialize proof : TraceOption ←
  registerTraceOption `proof false
    "(aesop) If the search is successful, print the produced proof term."

initialize profile : TraceOption ←
  registerTraceOption `profile false
    "(aesop) Print execution times for various parts of the tactic."

initialize steps : TraceOption ←
  registerTraceOption `steps false
    "(aesop) Print actions taken by Aesop during the proof search. Set the trace.aesop.steps.* options to choose which actions are printed."

initialize Init.stepsActiveGoalQueue : TraceOption ←
  registerTraceOption `steps.activeGoalQueue false
    "(aesop) Print the active goal queue after each iteration of the search loop. Has no effect unless trace.aesop.steps is true."

initialize Init.stepsBranchStates : TraceOption ←
  registerTraceOption `steps.branchStates false
    "(aesop) Print a rule's branch state before and after the rule is applied. Has no effect unless trace.aesop.steps is true."

initialize Init.stepsNormalization : TraceOption ←
  registerTraceOption `steps.normalization false
    "(aesop) Print intermediate goals during normalization. Has no effect unless trace.aesop.steps is true."

initialize Init.stepsRuleFailures : TraceOption ←
  registerTraceOption `steps.ruleFailures false
    "(aesop) When a rule fails, print the error message. Has no effect unless trace.aesop.steps is true."

initialize Init.stepsRuleSelection : TraceOption ←
  registerTraceOption `steps.ruleSelection false
    "(aesop) Print the rules selected for each goal. Has no effect unless trace.aesop.steps is true."

initialize Init.stepsTree : TraceOption ←
  registerTraceOption `steps.tree false
    "(aesop) Print the search tree after each iteration of the search loop. Has no effect unless trace.aesop.steps is true."

end TraceOption


-- A TraceModifier determines *how* a certain piece of information is printed.
structure TraceModifier where
  option : Lean.Option Bool
  deriving Inhabited

def registerTraceModifier (traceName : Name) (defValue : Bool) (descr : String) :
    IO TraceModifier := do
  let opt ←
    Option.register (`trace.aesop ++ traceName)
      { defValue := defValue, group := "trace", descr := descr }
  return { option := opt }

namespace TraceModifier

initialize goals : TraceModifier ←
  registerTraceModifier `goals true
    "(aesop) When printing a goal node, print the hypotheses and target."

initialize unsafeQueues : TraceModifier ←
  registerTraceModifier `unsafeQueues false
    "(aesop) When printing a goal node, print the unsafe rule queue."

initialize failedRapps : TraceModifier ←
  registerTraceModifier `failedRuleApplications false
    "(aesop) When printing a goal node, print the failed rule applications."

end TraceModifier

end Aesop
