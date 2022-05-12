/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule
import Lean

open Lean
open Lean.Meta

namespace Aesop

inductive RuleBuilderKind
  | global (decl : Name)
  | «local» (fvarUserName : Name) (goal : MVarId)

def RuleBuilderKind.toRuleIdent : RuleBuilderKind → RuleIdent
  | global decl => RuleIdent.const decl
  | «local» fvarUserName .. => RuleIdent.fvar fvarUserName

structure RuleBuilderInput where
  phase : PhaseName
  kind : RuleBuilderKind

structure RegularRuleBuilderResult where
  builder : BuilderName
  tac : RuleTacDescr
  indexingMode : IndexingMode
  mayUseBranchState : Bool
  deriving Inhabited

structure GlobalSimpRuleBuilderResult where
  builder : BuilderName
  entries : Array SimpEntry

structure LocalSimpRuleBuilderResult where
  builder : BuilderName
  originalFVarUserName : Name
  copiedFVarUserName : Name

inductive RuleBuilderResult
  | regular (r : RegularRuleBuilderResult)
  | globalSimp (r : GlobalSimpRuleBuilderResult)
  | localSimp (r : LocalSimpRuleBuilderResult)
  deriving Inhabited

inductive RuleBuilderOutput
  | global (r : RuleBuilderResult)
  | «local» (goal : MVarId) (r : RuleBuilderResult)

/--
Invariant: if the `RuleBuilderInput` contains a `RuleBuilderKind.local`,
then the builder returns a `RuleBuilderOutput.local`, and similar for
`RuleBuilderKind.global`.
-/
abbrev RuleBuilder := RuleBuilderInput → MetaM RuleBuilderOutput

namespace RuleBuilder

def checkConstIsInductive (builderName : BuilderName) (decl : Name) :
    MetaM InductiveVal := do
  let (some info) ← getConst? decl
    | throwError "aesop: {builderName} builder: unknown constant '{decl}'"
  let (ConstantInfo.inductInfo info) ← pure info
    | throwError "aesop: {builderName} builder: expected '{decl}' to be an inductive type"
  return info

def ofGlobalRuleBuilder (name : BuilderName)
    (globalBuilder : PhaseName → Name → MetaM RuleBuilderResult) :
    RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.local .. =>
    throwError "aesop: {name} builder does not support local hypotheses"
  | RuleBuilderKind.global decl =>
    RuleBuilderOutput.global <$> globalBuilder input.phase decl

end RuleBuilder

-- Options shared by all regular (meaning non-simp) builders.
structure RegularBuilderOptions where
  indexingMode? : Option IndexingMode
  deriving Inhabited

namespace RegularBuilderOptions

protected def default : RegularBuilderOptions where
  indexingMode? := none

def getIndexingModeM [Monad m] (dflt : m IndexingMode)
    (opts : RegularBuilderOptions) : m IndexingMode :=
  match opts.indexingMode? with
  | none => dflt
  | some imode => return imode

end RegularBuilderOptions
