/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Options
import Aesop.Script
import Std.Lean.Meta.SavedState

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop


/-! # Rule Tactic Types -/

/--
Input for a rule tactic. Contains:

- `goal`: the goal on which the rule is run.
- `mvars`: the set of mvars which occur in `goal`.
- `indexMatchLocations`: if the rule is indexed, the locations (e.g. hyps or the
  target) matched by the rule's index entries. Otherwise an empty set.
-/
structure RuleTacInput where
  goal : MVarId
  mvars : UnorderedArraySet MVarId
  indexMatchLocations : UnorderedArraySet IndexMatchLocation
  options : Options'
  deriving Inhabited

/--
A single rule application, representing the application of a tactic to the input
goal. Must accurately report the following information:

- `goals`: the goals generated by the tactic.
- `postState`: the `MetaM` state after the tactic was run.
- `scriptBuilder?`: script builder for the tactic. If
  `input.options.generateScript = false` (where `input` is the `RuleTacInput`),
  this field is ignored, so you can use `none`. If the tactic does not support
  script generation, also use `none`.
-/

structure RuleApplication where
  goals : Array MVarId
  postState : Meta.SavedState
  scriptBuilder? : Option RuleTacScriptBuilder

namespace RuleApplication

def check (r : RuleApplication) : MetaM (Option MessageData) :=
  r.postState.runMetaM' do
    for goal in r.goals do
      if ← goal.isAssignedOrDelayedAssigned then
        return some m!"subgoal metavariable {goal.name} is already assigned."
    return none

end RuleApplication

/--
The result of a rule tactic is a list of rule applications.
-/
structure RuleTacOutput where
  applications : Array RuleApplication
  deriving Inhabited

/--
A `RuleTac` is the tactic that is run when a rule is applied to a goal.
-/
def RuleTac := RuleTacInput → MetaM RuleTacOutput

instance : Inhabited RuleTac := by
  unfold RuleTac; exact inferInstance

/--
A `RuleTac` which generates only a single `RuleApplication`.
-/
def SingleRuleTac :=
  RuleTacInput → MetaM (Array MVarId × Option RuleTacScriptBuilder)

@[inline]
def SingleRuleTac.toRuleTac (t : SingleRuleTac) : RuleTac := λ input => do
  let (goals, scriptBuilder?) ← t input
  let postState ← saveState
  return ⟨#[{ postState, goals, scriptBuilder? }]⟩

@[inline]
def RuleTac.ofSingleRuleTac := SingleRuleTac.toRuleTac


/-! # Rule Tactic Descriptions -/

def CasesPattern := AbstractMVarsResult
  deriving Inhabited

inductive CasesTarget
  | decl (decl : Name)
  | patterns (patterns : Array CasesPattern)
  deriving Inhabited

inductive RuleTacDescr
  | applyConst (decl     : Name) (md : TransparencyMode)
  | applyFVar  (userName : Name) (md : TransparencyMode)
  | constructors (constructorNames : Array Name) (md : TransparencyMode)
  | neuralProvers
  | forwardConst (decl     : Name) (immediate : UnorderedArraySet Nat)
      (clear : Bool) (md : TransparencyMode)
  | forwardFVar  (userName : Name) (immediate : UnorderedArraySet Nat)
      (clear : Bool) (md : TransparencyMode)
  | cases (target : CasesTarget) (md : TransparencyMode)
      (isRecursiveType : Bool)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | singleRuleTac (decl : Name)
  | preprocess
  deriving Inhabited

namespace RuleTacDescr

def isGlobal : RuleTacDescr → Bool
  | applyConst .. => true
  | applyFVar .. => false
  | constructors .. => true
  | neuralProvers .. => true
  | forwardConst .. => true
  | forwardFVar .. => false
  | cases .. => true
  | tacticM .. => true
  | ruleTac .. => true
  | singleRuleTac .. => true
  | preprocess => true

end RuleTacDescr

end Aesop
