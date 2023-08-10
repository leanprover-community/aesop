/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std.Lean.Meta.SavedState

open Lean Lean.Meta

namespace Aesop.EqualUpToIds

-- TODO caching -- but maybe the ptrEq optimisation is enough

initialize registerTraceClass `Aesop.Util.EqualUpToIds

namespace EqualUpToIdsM

structure Context where
  commonMCtx : MetavarContext
  mctx₁ : MetavarContext
  mctx₂ : MetavarContext

structure State where
  equalMVarIds : HashMap MVarId MVarId := {}
  equalLMVarIds : HashMap LMVarId LMVarId := {}

end EqualUpToIdsM


abbrev EqualUpToIdsM :=
  ReaderT EqualUpToIdsM.Context $ StateRefT EqualUpToIdsM.State MetaM

def readCommonMCtx : EqualUpToIdsM MetavarContext :=
  return (← read).commonMCtx

def readMCtx₁ : EqualUpToIdsM MetavarContext :=
  return (← read).mctx₁

def readMCtx₂ : EqualUpToIdsM MetavarContext :=
  return (← read).mctx₂

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
@[inline, always_inline]
instance : Monad EqualUpToIdsM :=
  { inferInstanceAs (Monad EqualUpToIdsM) with }

protected def EqualUpToIdsM.run (x : EqualUpToIdsM α)
    (commonMCtx mctx₁ mctx₂ : MetavarContext) :
    MetaM α :=
  (·.fst) <$> (x { commonMCtx, mctx₁, mctx₂ }).run {}

structure GoalContext where
  mdecl₁ : MetavarDecl
  mdecl₂ : MetavarDecl
  equalFVarIds : HashMap FVarId FVarId := {}

inductive MVarValue where
  | mvarId (mvarId : MVarId)
  | expr (e : Expr)
  | delayedAssignment (da : DelayedMetavarAssignment)

namespace Unsafe

mutual
  unsafe def levelsEqualUpToIdsCore (l₁ l₂ : Level) : EqualUpToIdsM Bool :=
    if ptrEq l₁ l₂ then
      return true
    else
      levelsEqualUpToIdsCore' l₁ l₂

  unsafe def levelsEqualUpToIdsCore' : Level → Level → EqualUpToIdsM Bool
    | .zero, .zero => return true
    | .succ l₁, .succ l₂ => levelsEqualUpToIdsCore l₁ l₂
    | .max l₁ m₁, .max l₂ m₂ =>
      levelsEqualUpToIdsCore l₁ l₂ <&&> levelsEqualUpToIdsCore m₁ m₂
    | .imax l₁ m₁, .imax l₂ m₂ =>
      levelsEqualUpToIdsCore l₁ l₂ <&&> levelsEqualUpToIdsCore m₁ m₂
    | .param n₁, .param n₂ =>
      return n₁ == n₂
    | .mvar m₁, .mvar m₂ => do
      let commonMCtx := (← read).commonMCtx
      if commonMCtx.lDepth.contains m₁ || commonMCtx.lDepth.contains m₂ then
        return m₁ == m₂
      if let some m₂' := (← get).equalLMVarIds.find? m₁ then
        return m₂' == m₂
      else
        modify λ s => { s with equalLMVarIds := s.equalLMVarIds.insert m₁ m₂ }
        return true
    | _, _ => return false
end

end Unsafe

@[implemented_by Unsafe.levelsEqualUpToIdsCore]
opaque levelsEqualUpToIdsCore (l₁ l₂ : Level) : EqualUpToIdsM Bool

private def namesEqualUpToMacroScopes (n₁ n₂ : Name) : Bool :=
  n₁.hasMacroScopes == n₂.hasMacroScopes &&
  n₁.eraseMacroScopes == n₂.eraseMacroScopes

private def lctxDecls (lctx : LocalContext) : Array LocalDecl :=
  lctx.foldl (init := Array.mkEmpty lctx.numIndices) λ decls d =>
    if d.isImplementationDetail then decls else decls.push d

namespace Unsafe

mutual
  unsafe def exprsEqualUpToIdsCore (e₁ e₂ : Expr) :
      ReaderT GoalContext EqualUpToIdsM Bool := do
    withTraceNodeBefore `Aesop.Util.EqualUpToIds (return m!"comparing exprs {← printExpr (← readMCtx₁) (← read).mdecl₁ e₁}, {← printExpr (← readMCtx₂) (← read).mdecl₂ e₂}") do
      if ptrEq e₁ e₂ then
        return true
      else
        exprsEqualUpToIdsCore' (← instMVars (← readMCtx₁) e₁)
          (← instMVars (← readMCtx₂) e₂)
  where
    instMVars (mctx : MetavarContext) (e : Expr) : MetaM Expr :=
      withMCtx mctx (instantiateMVars e)

    printExpr (mctx : MetavarContext) (mdecl : MetavarDecl) (e : Expr) :
        MetaM MessageData :=
      withMCtx mctx do
        withLCtx mdecl.lctx mdecl.localInstances do
          addMessageContext m!"{e}"

  unsafe def exprsEqualUpToIdsCore' :
      Expr → Expr → ReaderT GoalContext EqualUpToIdsM Bool
    | .bvar i, .bvar j => return i == j
    | .fvar fvarId₁, .fvar fvarId₂ =>
      return (← read).equalFVarIds.find? fvarId₁ == some fvarId₂
    | .sort u, .sort v => levelsEqualUpToIdsCore u v
    | .const decl₁ lvls₁, .const decl₂ lvls₂ => do
      if decl₁ == decl₂ && lvls₁.length == lvls₂.length then
        for l₁ in lvls₁, l₂ in lvls₂ do
          if ! (← levelsEqualUpToIdsCore l₁ l₂) then
            return false
        return true
      else
        return false
    | .app f₁ x₁, .app f₂ x₂ =>
      exprsEqualUpToIdsCore f₁ f₂ <&&> exprsEqualUpToIdsCore x₁ x₂
    | .lam n₁ t₁ e₁ bi₁, .lam n₂ t₂ e₂ bi₂ =>
      pure (n₁ == n₂ && bi₁ == bi₂) <&&>
      exprsEqualUpToIdsCore t₁ t₂ <&&>
      exprsEqualUpToIdsCore e₁ e₂
    | .forallE n₁ t₁ e₁ bi₁, .forallE n₂ t₂ e₂ bi₂ =>
      pure (n₁ == n₂ && bi₁ == bi₂) <&&>
      exprsEqualUpToIdsCore t₁ t₂ <&&>
      exprsEqualUpToIdsCore e₁ e₂
    | .letE n₁ t₁ v₁ e₁ _, .letE n₂ t₂ v₂ e₂ _ =>
      pure (n₁ == n₂) <&&>
      exprsEqualUpToIdsCore t₁ t₂ <&&>
      exprsEqualUpToIdsCore v₁ v₂ <&&>
      exprsEqualUpToIdsCore e₁ e₂
    | .lit l₁, .lit l₂ => return l₁ == l₂
    | .mdata _ e₁, e₂ => exprsEqualUpToIdsCore e₁ e₂
    | e₁, .mdata _ e₂ => exprsEqualUpToIdsCore e₁ e₂
    | .proj n₁ i₁ e₁, .proj n₂ i₂ e₂ =>
      pure (n₁ == n₂ && i₁ == i₂) <&&> exprsEqualUpToIdsCore e₁ e₂
    | .mvar m₁, .mvar m₂ => do
      let v₁ ← normalizeMVar (← readMCtx₁) m₁
      let v₂ ← normalizeMVar (← readMCtx₂) m₂
      compareMVarValues v₁ v₂
    | .mvar m₁, e₂ => do
      let v₁ ← normalizeMVar (← readMCtx₁) m₁
      compareMVarValues v₁ (.expr e₂)
    | e₁, .mvar m₂ => do
      let v₂ ← normalizeMVar (← readMCtx₂) m₂
      compareMVarValues (.expr e₁) v₂
    | _, _ => return false
  where
    normalizeMVar (mctx : MetavarContext) (m : MVarId) : MetaM MVarValue :=
      withMCtx mctx do
        if let some dAss ← getDelayedMVarAssignment? m then
          return .delayedAssignment dAss
        else
          return .mvarId m

    compareMVarValues :
        (v₁ v₂ : MVarValue) → ReaderT GoalContext EqualUpToIdsM Bool
      | .expr e₁, .expr e₂ => exprsEqualUpToIdsCore e₁ e₂
      | .mvarId m₁, .mvarId m₂ => unassignedMVarsEqualUpToIdsCore m₁ m₂
      | .delayedAssignment dAss₁, .delayedAssignment dAss₂ =>
        unassignedMVarsEqualUpToIdsCore dAss₁.mvarIdPending dAss₂.mvarIdPending
        -- I'm not sure whether this suffices -- do we also need to check that
        -- the `fvars` in `dAss₁` correspond to the `fvars` in `dAss₂`?
      | _, _ => return false

  unsafe def localDeclsEqualUpToIdsCore :
      LocalDecl → LocalDecl → ReaderT GoalContext EqualUpToIdsM Bool
    | .cdecl _ _ userName₁ type₁ bi₁ kind₁,
      .cdecl _ _ userName₂ type₂ bi₂ kind₂ =>
      pure (namesEqualUpToMacroScopes userName₁ userName₂ && bi₁ == bi₂ &&
            kind₁ == kind₂) <&&>
      exprsEqualUpToIdsCore type₁ type₂
    | .ldecl _ _ userName₁ type₁ v₁ _ kind₁,
      .ldecl _ _ userName₂ type₂ v₂ _ kind₂ =>
      pure (namesEqualUpToMacroScopes userName₁ userName₂ &&
            kind₁ == kind₂) <&&>
      exprsEqualUpToIdsCore type₁ type₂ <&&>
      exprsEqualUpToIdsCore v₁ v₂
    | _, _ => return false

  unsafe def localContextsEqualUpToIdsCore (mdecl₁ mdecl₂ : MetavarDecl) :
      EqualUpToIdsM (Option GoalContext) := do
    let decls₁ := lctxDecls mdecl₁.lctx
    let decls₂ := lctxDecls mdecl₂.lctx
    if h : decls₁.size = decls₂.size then
      go decls₁ decls₂ h 0 { mdecl₁, mdecl₂ }
    else
      trace[Aesop.Util.EqualUpToIds] "number of hyps differs"
      return none
  where
    go (decls₁ decls₂ : Array LocalDecl) (h : decls₁.size = decls₂.size)
        (i : Nat) (gctx : GoalContext) : EqualUpToIdsM (Option GoalContext) := do
      if h' : i < decls₁.size then
        let ldecl₁ := decls₁[i]
        let ldecl₂ := decls₂[i]'(by simp [← h, h'])
        withTraceNodeBefore `Aesop.Util.EqualUpToIds (return m!"comparing hyps {ldecl₁.userName}, {ldecl₂.userName}") do
          if ! (← localDeclsEqualUpToIdsCore ldecl₁ ldecl₂ |>.run gctx) then
            return none
          else
            let equalFVarIds :=
              gctx.equalFVarIds.insert ldecl₁.fvarId ldecl₂.fvarId
            go decls₁ decls₂ h (i + 1) { gctx with equalFVarIds }
      else
        return some gctx

  unsafe def unassignedMVarsEqualUpToIdsCore (mvarId₁ mvarId₂ : MVarId) :
      EqualUpToIdsM Bool :=
    withTraceNodeBefore `Aesop.Util.EqualUpToIds (return m!"comparing mvars {mvarId₁.name}, {mvarId₂.name}") do
      let commonMCtx ← readCommonMCtx
      if commonMCtx.decls.contains mvarId₁ || commonMCtx.decls.contains mvarId₂ then
        if mvarId₁ == mvarId₂ then
          trace[Aesop.Util.EqualUpToIds] "common mvars are identical"
          return true
        else
          trace[Aesop.Util.EqualUpToIds] "common mvars are different"
          return false
      else if let some m₂ := (← get).equalMVarIds.find? mvarId₁ then
        if mvarId₂ == m₂ then
          trace[Aesop.Util.EqualUpToIds] "mvars already known to be equal"
          return true
        else
          trace[Aesop.Util.EqualUpToIds] "mvar {mvarId₁.name} known to be equal to different mvar {m₂.name}"
          return false
      else
        let ctx ← read
        let (some mdecl₁) := ctx.mctx₁.decls.find? mvarId₁ | throwError
          "unknown metavariable '?{mvarId₁.name}'"
        let (some mdecl₂) := ctx.mctx₂.decls.find? mvarId₂ | throwError
          "unknown metavariable '?{mvarId₂.name}'"
          if let some gctx ← localContextsEqualUpToIdsCore mdecl₁ mdecl₂ then
          withTraceNodeBefore `Aesop.Util.EqualUpToIds (return m!"comparing targets") do
            if ← exprsEqualUpToIdsCore mdecl₁.type mdecl₂.type |>.run gctx then
              modify λ s =>
                { s with equalMVarIds := s.equalMVarIds.insert mvarId₁ mvarId₂ }
              return true
            else
              return false
        else
          return false
end

end Unsafe

@[implemented_by Unsafe.unassignedMVarsEqualUpToIdsCore]
opaque unassignedMVarsEqualUpToIdsCore (mvarId₁ mvarId₂ : MVarId) :
    EqualUpToIdsM Bool

def tacticStatesEqualUpToIdsCore (goals₁ goals₂ : Array MVarId) :
    EqualUpToIdsM Bool := do
  if goals₁.size != goals₂.size then
    return false
  for g₁ in goals₁, g₂ in goals₂ do
    if ! (← unassignedMVarsEqualUpToIdsCore g₁ g₂) then
      return false
  return true

end EqualUpToIds

def unassignedMVarsEqualUptoIds (commonMCtx mctx₁ mctx₂ : MetavarContext)
    (mvarId₁ mvarId₂ : MVarId) : MetaM Bool := do
  EqualUpToIds.unassignedMVarsEqualUpToIdsCore mvarId₁ mvarId₂
    |>.run commonMCtx mctx₁ mctx₂

def tacticStatesEqualUpToIds (commonMCtx mctx₁ mctx₂ : MetavarContext)
    (goals₁ goals₂ : Array MVarId) : MetaM Bool := do
  EqualUpToIds.tacticStatesEqualUpToIdsCore goals₁ goals₂
    |>.run commonMCtx mctx₁ mctx₂

open Lean.Elab.Tactic in
def runTacticMCapturingPostState (t : TacticM Unit) (preState : Meta.SavedState)
    (preGoals : List MVarId) : MetaM (Meta.SavedState × List MVarId) :=
  withoutModifyingState do
    let go : TacticM (Meta.SavedState × List MVarId) := do
      preState.restore
      t
      pruneSolvedGoals
      let postState ← show MetaM _ from saveState
      let postGoals ← getGoals
      pure (postState, postGoals)
    go |>.run { elaborator := .anonymous, recover := false }
       |>.run' { goals := preGoals }
       |>.run'

end Aesop
