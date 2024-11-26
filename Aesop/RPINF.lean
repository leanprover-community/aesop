import Aesop.Util.Basic
import Aesop.BaseM

open Lean Lean.Meta

namespace Aesop

local instance : MonadCache Expr Expr BaseM where
  findCached? e :=
    return (← MonadCache.findCached? e : Option RPINFRaw).map (·.toExpr)
  cache k v := MonadCache.cache k (⟨v⟩ : RPINFRaw)

@[specialize]
partial def rpinfRaw (e : Expr) : BaseM RPINFRaw :=
  withReducible do return ⟨← go e⟩
where
  go (e : Expr) : BaseM Expr :=
    withIncRecDepth do
    checkCache e λ _ => do
      if ← isProof e then
        return .mdata (mdataSetIsProof {}) e
      let e ← whnf e
      match e with
      | .app .. =>
          let f ← go e.getAppFn'
          let mut args := e.getAppArgs'
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
      | .sort .. | .mvar .. | .lit .. | .const .. | .fvar .. =>
        return e
      | .letE .. | .mdata .. | .bvar .. => unreachable!

  withNewFVars {α} (fvars : Array Expr) (k : BaseM α) : BaseM α := do
    let mut lctx ← (getLCtx : MetaM _)
    for fvar in fvars do
      let fvarId := fvar.fvarId!
      let ldecl ← fvarId.getDecl
      let ldecl := ldecl.setType $ ← go ldecl.type
      lctx := lctx.modifyLocalDecl fvarId λ _ => ldecl
    withLCtx lctx (← getLocalInstances) k

def rpinf (e : Expr) : BaseM RPINF :=
  withConstAesopTraceNode .rpinf (return m!"rpinf") do
    aesop_trace[rpinf] "input:{indentExpr e}"
    let e ← rpinfRaw e
    let hash := pinfHash e.toExpr
    aesop_trace[rpinf] "result hash: {hash}"
    aesop_trace[rpinf] "resut:{indentExpr e.toExpr}"
    return { e with hash }

end Aesop
