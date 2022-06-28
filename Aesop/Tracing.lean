/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Tracing.Init

open Lean

namespace Aesop

variable [Monad m] [MonadOptions m]

namespace TraceOption

def isEnabled' (opt : TraceOption) (opts : Options) : Bool :=
  match opt.parentOption with
  | none => opt.option.get opts
  | some parent => parent.get opts && opt.option.get opts

def isEnabled (opt : TraceOption) : m Bool :=
  return opt.isEnabled' (← getOptions)

macro "aesop_trace![" opt:ident "]"
    s:(interpolatedStr(term) <|> term) : doElem => do
  let opt := mkIdentFrom opt $ `Aesop.TraceOption ++ opt.getId
  let msg ← do
    let s := s.raw
    if s.getKind == interpolatedStrKind then
      `(m! $(⟨s⟩))
    else
      `(($(⟨s⟩) : MessageData))
  `(doElem| do Lean.addTrace (Aesop.TraceOption.traceName $opt) $msg)

macro "aesop_trace[" opt:ident "]"
    s:(interpolatedStr(term) <|> Parser.Term.do <|> term) : doElem => do
  let optFull := mkIdentFrom opt $ `Aesop.TraceOption ++ opt.getId
  match s with
  | `(do $action) =>
    `(doElem| do
      if ← Aesop.TraceOption.isEnabled $optFull then
        $action)
  | _ =>
    let msg ← do
      let s := s.raw
      if s.getKind == interpolatedStrKind then
        `(m! $(⟨s⟩))
      else
        `(($(⟨s⟩) : MessageData))
    `(doElem| do
      if ← Aesop.TraceOption.isEnabled $optFull then
        aesop_trace![$opt] $msg)

-- The following slightly weird setup with the `Init.*` TraceOptions is
-- necessary because when we define something via `initialize`, we can't
-- evaluate that thing in the module where it was initialised. We therefore
-- can't use `steps.option` in the `Init` module.

@[inline]
def stepsActiveGoalQueue : TraceOption :=
  { Init.stepsActiveGoalQueue with parentOption := steps.option }

@[inline]
def stepsBranchStates : TraceOption :=
  { Init.stepsBranchStates with parentOption := steps.option }

@[inline]
def stepsNormalization : TraceOption :=
  { Init.stepsNormalization with parentOption := steps.option }

@[inline]
def stepsRuleFailures : TraceOption :=
  { Init.stepsRuleFailures with parentOption := steps.option }

@[inline]
def stepsRuleSelection : TraceOption :=
  { Init.stepsRuleSelection with parentOption := steps.option }

@[inline]
def stepsTree : TraceOption :=
  { Init.stepsTree with parentOption := steps.option }

@[inline]
def stepsProfile : TraceOption :=
  { Init.stepsProfile with parentOption := steps.option }

end TraceOption


namespace TraceModifier

@[inline]
def isEnabled' (opts : Options) (mod : TraceModifier) : Bool :=
  mod.option.get opts

@[inline]
def isEnabled (mod : TraceModifier) : m Bool :=
  return mod.isEnabled' (← getOptions)

end TraceModifier


structure TraceModifiers where
  goals : Bool
  unsafeQueues : Bool
  failedRapps : Bool

def TraceModifiers.get : m TraceModifiers := do
  let opts ← getOptions
  return {
    goals := TraceModifier.goals.isEnabled' opts
    unsafeQueues := TraceModifier.unsafeQueues.isEnabled' opts
    failedRapps := TraceModifier.failedRapps.isEnabled' opts
  }

end Aesop
