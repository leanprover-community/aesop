/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Basic

open Lean
open Lean.Meta
open Std (HashSet)

namespace Aesop

structure ForwardBuilderOptions where
  immediateHyps : Option (Array Name)
  clear : Bool
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
    (immediate : UnorderedArraySet Nat) (collectUsedHyps : Bool) :
    MetaM (Array Expr × Array FVarId) := do
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

    loop app instMVars immediateMVars 0 #[] #[] #[]
  where
    loop (app : Expr) (instMVars : Array MVarId) (immediateMVars : Array MVarId)
        (i : Nat) (proofsAcc : Array Expr) (currentUsedHyps : Array FVarId)
        (usedHypsAcc : Array FVarId) :
        MetaM (Array Expr × Array FVarId) := do
      if h : i < immediateMVars.size then
        let mvarId := immediateMVars.get ⟨i, h⟩
        let type ← getMVarType mvarId
        (← getLCtx).foldlM (init := (proofsAcc, usedHypsAcc)) λ s@(proofsAcc, usedHypsAcc) ldecl =>
          if ldecl.isAuxDecl then
            pure s
          else
            withoutModifyingState do
              if ← isDefEq ldecl.type type then
                assignExprMVar mvarId (mkFVar ldecl.fvarId)
                let currentUsedHyps :=
                  if collectUsedHyps then
                    currentUsedHyps.push ldecl.fvarId
                  else
                    currentUsedHyps
                loop app instMVars immediateMVars (i + 1) proofsAcc
                    currentUsedHyps usedHypsAcc
              else
                pure s
      else
        for instMVar in instMVars do
          withMVarContext instMVar do
            let inst ← synthInstance (← getMVarType instMVar)
            assignExprMVar instMVar inst
        let proofsAcc := proofsAcc.push (← abstractMVars app).expr
        let usedHypsAcc := usedHypsAcc ++ currentUsedHyps
        return (proofsAcc, usedHypsAcc)

def applyForwardRule (goal : MVarId) (e : Expr)
    (immediate : UnorderedArraySet Nat) (clear : Bool) : MetaM MVarId :=
  withMVarContext goal do
    let (newHyps, usedHyps) ←
      makeForwardHyps e immediate (collectUsedHyps := clear)
    if newHyps.isEmpty then
      throwError "while trying to apply {e} as a forward rule: found no viable instantiations for the immediate arguments"
    let userNames ← getUnusedUserNames newHyps.size `fwd
    let (_, goal) ← assertHypotheses goal $ ← newHyps.mapIdxM λ i val =>
      return {
        userName := userNames[i]
        value := val
        type := ← inferType val
      }
    if clear then
      tryClearMany' goal usedHyps
    else
      return goal

@[inline]
def forwardExpr (e : Expr) (immediate : UnorderedArraySet Nat) (clear : Bool) :
    RuleTac :=
  SimpleRuleTac.toRuleTac λ input => withMVarContext input.goal do
    let goal ← applyForwardRule input.goal e immediate clear
    return [goal]
    -- TODO optimise mvar analysis

def forwardConst (decl : Name) (immediate : UnorderedArraySet Nat)
    (clear : Bool) : RuleTac :=
  let tac := forwardExpr (mkConst decl) immediate clear
  if clear then
    tac
  else
    withApplicationLimit 1 tac
    -- TODO this is very crude

def forwardFVar (userName : Name) (immediate : UnorderedArraySet Nat)
    (clear : Bool) : RuleTac :=
  let tac := λ input => withMVarContext input.goal do
    let ldecl ← getLocalDeclFromUserName userName
    forwardExpr (mkFVar ldecl.fvarId) immediate clear input
  if clear then
    tac
  else
    withApplicationLimit 1 tac

end RuleTac


namespace GlobalRuleTacBuilder

def forwardCore (decl : Name)
    (immediate : UnorderedArraySet Nat) (clear : Bool) :
    GlobalRuleTacBuilder :=
  return {
    tac := RuleTac.forwardConst decl immediate clear
    descr := GlobalRuleTacBuilderDescr.forward decl immediate clear
  }

def forward (decl : Name)
    (immediate : Option (Array Name)) (clear : Bool) :
    GlobalRuleTacBuilder := do
  let immediate ← getImmediateNames (mkConst decl) immediate
  forwardCore decl immediate clear

end GlobalRuleTacBuilder


def RuleTacBuilder.forward (userName : Name) (immediate : Option (Array Name))
    (clear : Bool) : RuleTacBuilder := λ goal => do
  let (goal, #[newHyp]) ← copyRuleHypotheses goal #[userName]
    | unreachable!
  withMVarContext goal do
    let immediate ← getImmediateNames (mkFVar newHyp) immediate
    let tac :=
      { tac := RuleTac.forwardFVar (← getLocalDecl newHyp).userName immediate clear
        descr := none }
    return (goal, tac)

def RuleBuilder.forward (opts : ForwardBuilderOptions) :
    RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.global decl => do
    let tac ← GlobalRuleTacBuilder.forward decl opts.immediateHyps opts.clear
    return RuleBuilderOutput.global $ mkResult tac
  | RuleBuilderKind.local fvarUserName goal => do
    let (goal, tac) ←
      RuleTacBuilder.forward fvarUserName opts.immediateHyps opts.clear goal
    return RuleBuilderOutput.local (mkResult tac) goal
  where
    mkResult (tac : RuleTacWithBuilderDescr) : RuleBuilderResult :=
      RuleBuilderResult.regular {
        builder := BuilderName.forward
        tac := tac
        indexingMode := IndexingMode.unindexed -- TODO
        mayUseBranchState := true
      }

end Aesop
