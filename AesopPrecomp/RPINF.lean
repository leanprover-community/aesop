/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import AesopPrecomp.RPINF.Basic

open Lean Lean.Meta

namespace Aesop

variable [Monad m] [MonadRPINF m] [MonadControlT MetaM m] [MonadError m]
  [MonadRecDepth m] [MonadLiftT MetaM m] [MonadTrace m] [AddMessageContext m]
  [MonadOptions m] [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m]

local instance : MonadCache Expr Expr m where
  findCached? e :=
    return (← MonadCache.findCached? e : Option RPINFRaw).map (·.toExpr)
  cache k v := MonadCache.cache k (⟨v⟩ : RPINFRaw)

@[specialize]
partial def rpinfRaw (e : Expr) : m RPINFRaw :=
  withReducible do return ⟨← go e⟩
where
  go (e : Expr) : m Expr :=
    withIncRecDepth do
    checkCache e λ _ => do
      if ← isProof e then
        return .mdata (mdataSetIsProof {}) e
      let e ← whnf e
      match e with
      | .app .. =>
        let f ← go e.getAppFn'
        let mut args := e.getAppArgs
        for i in [:args.size] do
          let arg := args[i]!
          args := args.set! i default -- prevent nonlinear access to args[i]
          let arg ← go arg
          args := args.set! i arg
        if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
          return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
        else
          return mkAppN f args
      | .lam .. =>
        -- TODO disable cache?
        lambdaTelescope e λ xs e => withNewFVars xs do
          mkLambdaFVars xs (← go e)
      | .forallE .. =>
        -- TODO disable cache?
        forallTelescope e λ xs e => withNewFVars xs do
          mkForallFVars xs (← go e)
      | .proj t i e =>
        return .proj t i (← go e)
      | .sort u => return .sort <| ← normalizeLevel u
      | .const n us => return .const n <| ← us.mapM fun u => normalizeLevel u
      | .mvar .. | .lit .. | .fvar .. =>
        return e
      | .letE .. | .mdata .. | .bvar .. => unreachable!

  withNewFVars {α} (fvars : Array Expr) (k : m α) : m α := do
    let mut lctx ← (getLCtx : MetaM _)
    for fvar in fvars do
      let fvarId := fvar.fvarId!
      let ldecl ← fvarId.getDecl
      let ldecl := ldecl.setType $ ← go ldecl.type
      lctx := lctx.modifyLocalDecl fvarId λ _ => ldecl
    withLCtx lctx (← getLocalInstances) k

@[specialize]
def rpinfCore (e : Expr) : m RPINF :=
  withTraceNode `rpinf (fun _ => return m!"rpinf") do
    trace[rpinf] "input:{indentExpr e}"
    let e ← rpinfRaw e
    let hash := pinfHash e.toExpr
    trace[rpinf] "resut:{indentExpr e.toExpr}"
    trace[rpinf] "result hash: {hash}"
    return { e with hash }

end Aesop
