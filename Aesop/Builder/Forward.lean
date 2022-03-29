/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta

namespace Aesop

structure ForwardBuilderOptions where
  immediateHyps : Option (Array Name)
  deriving Inhabited

def getImmediateNames (e : Expr) : Option (Array Name) →
    MetaM (UnorderedArraySet Nat)
  | none => do
    -- If no immediate names are given, every argument becomes immediate,
    -- except instance args and dependent args.
    forallTelescope (← inferType e) λ args _ => do
      let mut result := #[]
      for i in [0:args.size] do
        let fvarId := args[i].fvarId!
        let ldecl ← getLocalDecl fvarId
        let isNondep : MetaM Bool :=
          args.allM (start := i + 1) λ arg =>
            return ! (← getLocalDecl arg.fvarId!).type.containsFVar fvarId
        if ← pure ! ldecl.binderInfo.isInstImplicit <&&> isNondep then
          result := result.push i
      return UnorderedArraySet.ofDeduplicatedArray result
  | some immediate => do
    -- If immediate names are given, we check that corresponding arguments
    -- exists and record these arguments' positions.
    forallTelescope (← inferType e) λ args _ => do
      let mut unseen := immediate.deduplicate (ord := ⟨Name.quickCmp⟩)
      let mut result := #[]
      for i in [0:args.size] do
        let argName := (← getLocalDecl args[i].fvarId!).userName
        if immediate.contains argName then
          result := result.push i
          unseen := unseen.erase argName
      if ! unseen.isEmpty then throwError
        "aesop: while registering '{e}' as a forward rule: function does not have arguments with these names: '{unseen}'"
      return UnorderedArraySet.ofDeduplicatedArray result

namespace RuleTac

private partial def makeForwardHyps (e : Expr)
    (immediate : UnorderedArraySet Nat) : MetaM (Array Expr) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (argMVars, binderInfos, conclusion) ← forallMetaTelescope type

    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for i in [0:argMVars.size] do
      let mvarId := argMVars[i].mvarId!
      let argName := (← getMVarDecl mvarId).userName
      if immediate.contains i then
        immediateMVars := immediateMVars.push mvarId
      else if binderInfos[i].isInstImplicit then
        instMVars := instMVars.push mvarId

    loop app instMVars immediateMVars 0 #[]
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
      if h : i < immediateMVars.size then
        let mvarId := immediateMVars.get ⟨i, h⟩
        let type := ← getMVarType mvarId

        (← getLCtx).foldlM (init := acc) λ acc ldecl => do
          if ldecl.isAuxDecl then
            return acc
          withoutModifyingState do
            if ← isDefEq ldecl.type type then
              assignExprMVar mvarId (mkFVar ldecl.fvarId)
              loop app instMVars immediateMVars (i + 1) acc
            else
              pure acc
      else
        for instMVar in instMVars do
          let mvarId := instMVar
          let decl ← getMVarDecl mvarId
          let inst ← synthInstance decl.type
          assignExprMVar mvarId inst
        return acc.push (← abstractMVars app).expr

def applyForwardRule (goal : MVarId) (e : Expr) (immediate : UnorderedArraySet Nat) :
    MetaM MVarId :=
  withMVarContext goal do
    let newHyps ← makeForwardHyps e immediate
    let userNames ← getUnusedUserNames newHyps.size `fwd
    let (_, goal) ← assertHypotheses goal $ ← newHyps.mapIdxM λ i val =>
      return {
        userName := userNames[i]
        value := val
        type := ← inferType val
      }
    return goal

@[inline]
def forwardExpr (e : Expr) (immediate : UnorderedArraySet Nat) : RuleTac :=
  SimpleRuleTac.toRuleTac λ input => withMVarContext input.goal do
    let goal ← applyForwardRule input.goal e immediate
    return {
      introducedMVars := IntroducedMVars.raw #[goal]
      assignedMVars? := none
      -- TODO optimise mvar analysis
    }

def forwardConst (decl : Name) (immediate : UnorderedArraySet Nat) : RuleTac :=
  withApplicationLimit 1 $ forwardExpr (mkConst decl) immediate

def forwardFVar (userName : Name) (immediate : UnorderedArraySet Nat) :
    RuleTac :=
  withApplicationLimit 1 λ input => withMVarContext input.goal do
    let ldecl ← getLocalDeclFromUserName userName
    forwardExpr (mkFVar ldecl.fvarId) immediate input

end RuleTac

def GlobalRuleTacBuilder.forwardCore (decl : Name) (immediate : UnorderedArraySet Nat) :
    GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.forwardConst decl immediate
    descr := GlobalRuleTacBuilderDescr.forward decl immediate
  }

def GlobalRuleTacBuilder.forward (decl : Name) (immediate : Option (Array Name)) :
    GlobalRuleTacBuilder := do
  let immediate ← getImmediateNames (mkConst decl) immediate
  return {
    tac := RuleTac.forwardConst decl immediate
    descr := GlobalRuleTacBuilderDescr.forward decl immediate
  }

def RuleTacBuilder.forward (userName : Name) (immediate : Option (Array Name)) :
    RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← copyRuleHypotheses goal #[userName] | unreachable!
  withMVarContext goal do
    let immediate ← getImmediateNames (mkFVar newHyp) immediate
    let tac :=
      { tac := RuleTac.forwardFVar (← getLocalDecl newHyp).userName immediate
        descr := none }
    return (goal, tac)

def GlobalRuleBuilder.forward (opts : ForwardBuilderOptions) :
    GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  return {
    builder := BuilderName.forward
    tac := ← GlobalRuleTacBuilder.forward decl opts.immediateHyps
    indexingMode := IndexingMode.unindexed -- TODO
    mayUseBranchState := false
  }

def LocalRuleBuilder.forward (opts : ForwardBuilderOptions) :
    LocalRuleBuilder RegularRuleBuilderResult := λ hypUserName goal => do
  let (goal, tac) ←
    RuleTacBuilder.forward hypUserName opts.immediateHyps goal
  let result := {
    builder := BuilderName.forward
    tac := tac
    indexingMode := IndexingMode.unindexed -- TODO
    mayUseBranchState := true
  }
  return (goal, result)

def RuleBuilder.forward (opts : ForwardBuilderOptions) :
    RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder (GlobalRuleBuilder.forward opts)
    (LocalRuleBuilder.forward opts)

end Aesop
