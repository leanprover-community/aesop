/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.Options
import Aesop.Percent
import Aesop.Script.CtorNames
import Aesop.Script.Step
import Batteries.Lean.Meta.SavedState

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
- `patternInstantiations`: if the rule has a pattern, the pattern instantiations
  that were found in the goal. Each instantiation is a list of expressions which
  were found by matching the pattern against expressions in the goal. For
  example, if `h : max a b = max a c` appears in the goal and the rule has
  pattern `max x y`, there will be two pattern instantiations `[a, b]`
  (representing the substitution `{x ↦ a, y ↦ b}`) and `[a, c]`. If the rule
  does not have a pattern, `patternInstantiations` is empty; otherwise it's
  guaranteed to be non-empty.
- `options`: the options given to Aesop.
-/
structure RuleTacInput where
  goal : MVarId
  mvars : UnorderedArraySet MVarId
  indexMatchLocations : HashSet IndexMatchLocation
  patternInstantiations : HashSet RulePatternInstantiation
  options : Options'
  deriving Inhabited

/--
A single rule application, representing the application of a tactic to the input
goal. Must accurately report the following information:

- `goals`: the goals generated by the tactic.
- `postState`: the `MetaM` state after the tactic was run.
- `scriptSteps?`: script steps which produce the same effect as the rule tactic.
  If `input.options.generateScript = false` (where `input` is the
  `RuleTacInput`), this field is ignored. If the tactic does not support script
  generation, use `none`.
- `successProbability`: The success probability of this rule application. If
  `none`, we use the success probability of the applied rule.
-/
structure RuleApplication where
  goals : Array MVarId
  postState : Meta.SavedState
  scriptSteps? : Option (Array Script.LazyStep)
  successProbability? : Option Percent

namespace RuleApplication

def check (r : RuleApplication) : MetaM (Option MessageData) :=
  r.postState.runMetaM' do
    for goal in r.goals do
      if ← goal.isAssignedOrDelayedAssigned then
        return some m!"subgoal metavariable {goal.name} is already assigned."
    return none

def ofLazyScriptStep (step : Script.LazyStep)
    (successProbability? : Option Percent) : RuleApplication where
  goals := step.postGoals
  postState := step.postState
  scriptSteps? := #[step]
  successProbability? := successProbability?

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
  RuleTacInput →
  MetaM (Array MVarId × Option (Array Script.LazyStep) × Option Percent)

@[inline]
def SingleRuleTac.toRuleTac (t : SingleRuleTac) : RuleTac := λ input => do
  let (goals, scriptSteps?, successProbability?) ← t input
  let postState ← saveState
  return ⟨#[{ postState, goals, scriptSteps?, successProbability? }]⟩

@[inline]
def RuleTac.ofSingleRuleTac := SingleRuleTac.toRuleTac

def RuleTac.ofTacticSyntax (t : RuleTacInput → MetaM Syntax.Tactic)
    (scriptSyntax? : Option (RuleTacInput → MetaM Syntax.Tactic) := none) :
    RuleTac :=
  RuleTac.ofSingleRuleTac λ input => do
    let stx ← t input
    let preState ← saveState
    let postGoals ← Lean.Elab.Tactic.run input.goal (evalTactic stx) |>.run'
    let postState ← saveState
    let postGoals := postGoals.toArray
    let stepStx ←
      match scriptSyntax? with
      | none => pure stx
      | some stxGen => stxGen input
    let step := {
      preGoal := input.goal
      tacticBuilders := #[return .unstructured stepStx]
      preState, postState, postGoals
    }
    return (postGoals, some #[step], none)

/--
A tactic generator is a special sort of rule tactic, intended for use with
generative machine learning methods. It generates zero or more tactics
(represented as strings) that could be applied to the goal, plus a success
probability for each tactic. When Aesop executes a tactic generator, it executes
each of the tactics and, if the tactic succeeds, adds a rule application for it.
The tactic's success probability (which must be between 0 and 1, inclusive)
becomes the success probability of the rule application. A `TacGen` rule
succeeds if at least one of its suggested tactics succeeds.
-/
abbrev TacGen := MVarId → MetaM (Array (String × Float))

/-! # Rule Tactic Descriptions -/

def CasesPattern := AbstractMVarsResult
  deriving Inhabited

inductive CasesTarget
  | decl (decl : Name)
  | patterns (patterns : Array CasesPattern)
  deriving Inhabited

inductive RuleTerm
  | const (decl : Name)
  | term (term : Term)

inductive RuleTacDescr
  | apply (term : RuleTerm) (md : TransparencyMode) (pat? : Option RulePattern)
  | constructors (constructorNames : Array Name) (md : TransparencyMode)
  | forward (term : RuleTerm) (pat? : Option RulePattern)
      (immediate : UnorderedArraySet Nat) (isDestruct : Bool)
      (md : TransparencyMode)
  | cases (target : CasesTarget) (md : TransparencyMode)
      (isRecursiveType : Bool) (ctorNames : Array CtorNames)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | tacGen (decl : Name)
  | singleRuleTac (decl : Name)
  | tacticStx (stx : Syntax)
  | preprocess
  deriving Inhabited

end Aesop
