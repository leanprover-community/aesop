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

structure RegularRuleBuilderResult where
  builder : BuilderName
  tac : RuleTacWithBuilderDescr
  indexingMode : IndexingMode
  mayUseBranchState : Bool
  deriving Inhabited

structure SimpRuleBuilderResult where
  builder : BuilderName
  entries : Array SimpEntry

inductive NormRuleBuilderResult
  | regular (r : RegularRuleBuilderResult)
  | simp (r : SimpRuleBuilderResult)
  deriving Inhabited


namespace IndexingMode

def targetMatchingConclusion (type : Expr) : MetaM IndexingMode := do
  let path ← withoutModifyingState do
    let (_, _, conclusion) ← forallMetaTelescope type
    DiscrTree.mkPath conclusion
    -- We use a meta telescope because `DiscrTree.mkPath` ignores metas (they
    -- turn into `Key.star`) but not fvars.
  return IndexingMode.target path

end IndexingMode


/--
A `GlobalRuleBuilder` takes the name of a global constant and produces a
`RegularRuleBuilderResult` or `NormRuleBuilderResult`.
-/
abbrev GlobalRuleBuilder α := Name → MetaM α

/--
A `LocalRuleBuilder` takes the `userName` of a hypothesis and produces a
`RegularRuleBuilderResult` or `NormRuleBuilderResult`. It operates on the given
goal and may change it.
-/
abbrev LocalRuleBuilder α := Name → MVarId → MetaM (MVarId × α)

/--
A `RuleBuilder` is either a `GobalRuleBuilder` or a `LocalRuleBuilder`
-/
abbrev RuleBuilder α := RuleIdent → MVarId → MetaM (MVarId × α)


structure TacticBuilderOptions where
  usesBranchState : Bool
  deriving Inhabited

def TacticBuilderOptions.default : TacticBuilderOptions where
  usesBranchState := true


namespace GlobalRuleBuilder

-- TODO We currently don't process unfold theorems and smart unfolding equations
-- (whatever that is). See SimpLemmas.lean:mkSimpAttr.
def normSimpUnfold : GlobalRuleBuilder NormRuleBuilderResult := λ decl => do
  let info ← getConstInfo decl
  unless info.hasValue do
    throwError "aesop: unfold builder: expected {decl} to be a definition to unfold"
  return NormRuleBuilderResult.simp
    { builder := BuilderName.unfold, entries := #[SimpEntry.toUnfold decl] }

def normSimpLemmas : GlobalRuleBuilder NormRuleBuilderResult := λ decl => do
  try {
    let simpLemmas ←
      mkSimpTheoremsFromConst decl (post := true) (inv := false) (prio := 0)
    return NormRuleBuilderResult.simp {
      builder := BuilderName.simp
      entries := simpLemmas.map SimpEntry.thm
    }
  } catch e => {
    throwError "aesop: simp builder: exception while trying to add {decl} as a simp lemma:{indentD e.toMessageData}"
  }

def apply : GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  return {
    builder := BuilderName.apply
    tac := ← GlobalRuleTacBuilder.apply decl
    indexingMode := ←
      IndexingMode.targetMatchingConclusion (← getConstInfo decl).type
    mayUseBranchState := false
  }

def tactic (opts : TacticBuilderOptions) :
    GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  return {
    builder := BuilderName.tactic
    tac := ← GlobalRuleTacBuilder.tactic decl
    indexingMode := IndexingMode.unindexed
    mayUseBranchState := opts.usesBranchState
  }

private def checkConstIsInductive (builderName : Name) (decl : Name) :
    MetaM InductiveVal := do
  let (some info) ← getConst? decl
    | throwError "aesop: {builderName} builder: unknown constant '{decl}'"
  let (ConstantInfo.inductInfo info) ← pure info
    | throwError "aesop: {builderName} builder: expected '{decl}' to be an inductive type"
  return info

def constructors : GlobalRuleBuilder RegularRuleBuilderResult := λ decl => do
  let info ← checkConstIsInductive `constructors decl
  return {
    builder := BuilderName.constructors
    tac := ← GlobalRuleTacBuilder.constructors info.ctors.toArray
    indexingMode := IndexingMode.unindexed -- TODO optimise as soon as we have OR for IndexingModes
    mayUseBranchState := false
  }

def cases : GlobalRuleBuilder RegularRuleBuilderResult := λ decl => do
  let builderName := `cases
  let inductInfo ← checkConstIsInductive builderName decl
  return {
    builder := BuilderName.cases
    tac := ← GlobalRuleTacBuilder.cases decl
      (isRecursiveType := inductInfo.isRec)
    indexingMode := IndexingMode.unindexed
    mayUseBranchState := false
  }

end GlobalRuleBuilder

private def throwDefaultBuilderFailure (ruleType : String) (id : Name) : MetaM α :=
  throwError "aesop: Unable to interpret {id} as {ruleType} rule. Try specifying a builder."

structure ForwardBuilderOptions where
  immediateHyps : Option (Array Name)
  deriving Inhabited

namespace GlobalRuleBuilder

def forward (opts : ForwardBuilderOptions) :
    GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  return {
    builder := BuilderName.forward
    tac := ← GlobalRuleTacBuilder.forward decl opts.immediateHyps
    indexingMode := IndexingMode.unindexed -- TODO
    mayUseBranchState := false
  }

-- TODO In the default builders below, we should distinguish between fatal and
-- nonfatal errors. E.g. if the `tactic` builder finds a declaration that is not
-- of tactic type, this is a nonfatal error and we should continue with the next
-- builder. But if the simp builder finds an equation that cannot be interpreted
-- as a simp lemma for some reason, this is a fatal error. Continuing with the
-- next builder is more confusing than anything because the user probably
-- intended to add a simp lemma.

def unsafeRuleDefault : GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  constructors decl <|>
  tactic TacticBuilderOptions.default decl <|>
  apply decl <|>
  throwDefaultBuilderFailure "an unsafe" decl

def safeRuleDefault : GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  constructors decl <|>
  tactic TacticBuilderOptions.default decl <|>
  apply decl <|>
  throwDefaultBuilderFailure "a safe" decl

def normRuleDefault : GlobalRuleBuilder NormRuleBuilderResult := λ decl =>
  NormRuleBuilderResult.regular <$> tactic TacticBuilderOptions.default decl <|>
  normSimpLemmas decl <|>
  NormRuleBuilderResult.regular <$> apply decl <|>
  throwDefaultBuilderFailure "a norm" decl

end GlobalRuleBuilder


namespace LocalRuleBuilder

def apply : LocalRuleBuilder RegularRuleBuilderResult := λ hypUserName goal => do
  let (goal, tac) ← RuleTacBuilder.applyFVar hypUserName goal
  withMVarContext goal do
    let type := (← getLocalDeclFromUserName hypUserName).type
    let result := {
      builder := BuilderName.apply
      tac := tac
      indexingMode := ← IndexingMode.targetMatchingConclusion type
      mayUseBranchState := false
    }
    return (goal, result)

def forward (opts : ForwardBuilderOptions) :
    LocalRuleBuilder RegularRuleBuilderResult := λ hypUserName goal => do
  let (goal, tac) ←
    RuleTacBuilder.forwardFVar hypUserName opts.immediateHyps goal
  let result := {
    builder := BuilderName.forward
    tac := tac
    indexingMode := IndexingMode.unindexed -- TODO
    mayUseBranchState := true
  }
  return (goal, result)

def unsafeRuleDefault : LocalRuleBuilder RegularRuleBuilderResult :=
  λ hypUserName goal =>
    apply hypUserName goal <|>
    throwDefaultBuilderFailure "an unsafe" hypUserName

def safeRuleDefault : LocalRuleBuilder RegularRuleBuilderResult :=
  λ hypUserName goal =>
    apply hypUserName goal <|>
    throwDefaultBuilderFailure "a safe" hypUserName

def normRuleDefault : LocalRuleBuilder NormRuleBuilderResult :=
  λ hypUserName goal =>
    throwError "aesop: Please specify a builder for norm rule {hypUserName}."

end LocalRuleBuilder


namespace RuleBuilder

def toGlobalRuleBuilder (r : RuleBuilder α) : GlobalRuleBuilder α := λ decl =>
  Prod.snd <$> r (RuleIdent.const decl) ⟨`_dummy⟩
  -- NOTE: We assume that the 'global part' of `r` does not use the `_dummy`
  -- mvar.

def toLocalRuleBuilder (r : RuleBuilder α) :
    LocalRuleBuilder α := λ fvarId goal =>
  r (RuleIdent.fvar fvarId) goal

def toNormRuleBuilder (r : RuleBuilder RegularRuleBuilderResult) :
    RuleBuilder NormRuleBuilderResult := λ id goal => do
  let (goal, res) ← r id goal
  return (goal, NormRuleBuilderResult.regular res)

def ofGlobalAndLocalRuleBuilder (global : GlobalRuleBuilder α)
    («local» : LocalRuleBuilder α) : RuleBuilder α := λ id goal => do
  match id with
  | RuleIdent.const const => return (goal, ← global const)
  | RuleIdent.fvar hyp => «local» hyp goal

def ofGlobalRuleBuilder (builderName : String) (global : GlobalRuleBuilder α) :
    RuleBuilder α :=
  ofGlobalAndLocalRuleBuilder global
    (λ _ _ => throwError
      "aesop: {builderName} builder: this builder does not support local hypotheses")

def normSimpUnfold : RuleBuilder NormRuleBuilderResult :=
  ofGlobalRuleBuilder "unfold" GlobalRuleBuilder.normSimpUnfold

def normSimpLemmas : RuleBuilder NormRuleBuilderResult :=
  ofGlobalRuleBuilder "simp" GlobalRuleBuilder.normSimpLemmas

def apply : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.apply LocalRuleBuilder.apply

def forward (opts : ForwardBuilderOptions) :
    RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder (GlobalRuleBuilder.forward opts)
    (LocalRuleBuilder.forward opts)

def tactic (opts : TacticBuilderOptions) :
    RuleBuilder RegularRuleBuilderResult :=
  ofGlobalRuleBuilder "tactic" $ GlobalRuleBuilder.tactic opts

def constructors : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalRuleBuilder "constructors" $ GlobalRuleBuilder.constructors

def cases : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalRuleBuilder "cases" $ GlobalRuleBuilder.cases

def unsafeDefault : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.unsafeRuleDefault
    LocalRuleBuilder.unsafeRuleDefault

def safeDefault : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.safeRuleDefault
    LocalRuleBuilder.safeRuleDefault

def normDefault : RuleBuilder NormRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.normRuleDefault
    LocalRuleBuilder.normRuleDefault

end Aesop.RuleBuilder
