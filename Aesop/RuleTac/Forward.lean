/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleTac.Basic

open Lean
open Lean.Meta

namespace Aesop.RuleTac

private partial def makeForwardHyps (e : Expr)
    (immediate : UnorderedArraySet Nat) (collectUsedHyps : Bool) :
    MetaM (Array Expr × Array FVarId) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (argMVars, binderInfos, _) ← forallMetaTelescopeReducing type

    let app := mkAppN e argMVars
    let mut instMVars := Array.mkEmpty argMVars.size
    let mut immediateMVars := Array.mkEmpty argMVars.size
    for i in [0:argMVars.size] do
      let mvarId := argMVars[i].mvarId!
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
def forwardExpr (e : Expr) (immediate : UnorderedArraySet Nat)
    (clear : Bool) : RuleTac :=
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

end Aesop.RuleTac
