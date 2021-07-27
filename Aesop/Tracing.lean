/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

-- TODO Instead of tracing, I think we want to construct a couple of big
-- messages at the end: one with the ruleset, one with the final search tree,
-- one with the steps taken (displayed in a nice structured manner and hopefully
-- inspectable).

import Lean.Util.Trace

open Lean

-- TODO This block currently has no effect since `registerTraceClass` only
-- works with builtin_initialize.
initialize
  registerTraceClass `Aesop.RuleSet
  registerTraceClass `Aesop.Steps
  registerTraceClass `Aesop.Steps.Goals
  registerTraceClass `Aesop.Steps.UnsafeQueues
  registerTraceClass `Aesop.Steps.FailedRuleApplications
  registerTraceClass `Aesop.Steps.RuleSelection
  registerTraceClass `Aesop.Steps.FinalProof
  registerTraceClass `Aesop.Steps.Normalization
  registerTraceClass `Aesop.Tree
  registerTraceClass `Aesop.Tree.Goals
  registerTraceClass `Aesop.Tree.UnsafeQueues
  registerTraceClass `Aesop.Tree.FailedRuleApplications

namespace Aesop

inductive TraceContext
  | steps
  | tree

namespace TraceContext

@[inlineIfReduce]
protected def toTraceOptionPrefix : TraceContext → Name
  | steps => `trace.Aesop.Steps
  | tree => `trace.Aesop.Tree

end TraceContext

inductive TraceOption : TraceContext → Type
  | showGoals : TraceOption c
  | showUnsafeQueues : TraceOption c
  | showFailedRapps : TraceOption c
  | showRuleSelection : TraceOption TraceContext.steps
  | showFinalProof : TraceOption TraceContext.steps
  | showNormalizationSteps : TraceOption TraceContext.steps

namespace TraceOption

@[inlineIfReduce]
protected def toTraceOptionSuffix {c} : TraceOption c → Name
  | showGoals => `Goals
  | showUnsafeQueues => `UnsafeQueues
  | showFailedRapps => `FailedRuleApplications
  | showRuleSelection => `RuleSelection
  | showFinalProof => `FinalProof
  | showNormalizationSteps => `Normalization

@[inline]
protected def default {c} : TraceOption c → Bool :=
  λ _ => true

@[inline]
def get [Monad m] [MonadOptions m] (c : TraceContext) (o : TraceOption c) :
    m Bool :=
  getBoolOption (c.toTraceOptionPrefix ++ o.toTraceOptionSuffix) o.default

end TraceOption

end Aesop
