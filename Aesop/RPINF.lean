import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

def mdataRPINFIsProofName : Name :=
  `Aesop.rpinfIsProof

def mdataSetIsProof (d : MData) : MData :=
  d.insert mdataRPINFIsProofName true

def mdataIsProof (d : MData) : Bool :=
  d.getBool mdataRPINFIsProofName (defVal := false)

mutual
  def rpinfEqCore : (x y : Expr) → Bool
    | .bvar i₁, .bvar i₂ => i₁ == i₂
    | .fvar id₁, .fvar id₂ => id₁ == id₂
    | .mvar id₁, .mvar id₂ => id₁ == id₂
    | .sort u, .sort v => u == v
    | .const n₁ us, .const n₂ vs => n₁ == n₂ && us == vs
    | .app f₁ e₁, .app f₂ e₂ => rpinfEq f₁ f₂ && rpinfEq e₁ e₂
    | .lam _ t₁ e₁ bi₁, .lam _ t₂ e₂ bi₂ =>
      bi₁ == bi₂ && rpinfEq t₁ t₂ && rpinfEq e₁ e₂
    | .forallE _ t₁ e₁ bi₁, .forallE _ t₂ e₂ bi₂ =>
      bi₁ == bi₂ && rpinfEq t₁ t₂ && rpinfEq e₁ e₂
    | .letE _ t₁ v₁ e₁ _, .letE _ t₂ v₂ e₂ _ =>
      rpinfEq v₁ v₂ && rpinfEq t₁ t₂ && rpinfEq e₁ e₂
    | .lit l₁, .lit l₂ => l₁ == l₂
    | .mdata d e₁, e₂ | e₁, .mdata d e₂ => mdataIsProof d || rpinfEq e₁ e₂
    | _, _ => false

  def rpinfEq (x y : Expr) : Bool :=
    (unsafe ptrEq x y) || rpinfEqCore x y
end

partial def rpinfHashCore (e : Expr) :
    StateRefT (Std.HashMap UInt64 UInt64) (ST s) UInt64 :=
  have : MonadHashMapCacheAdapter UInt64 UInt64
           (StateRefT (Std.HashMap UInt64 UInt64) (ST s)) := {
    getCache := get
    modifyCache := modify
  }
  checkCache e.hash λ _ => do
    match e with
    | .app .. =>
      let h ← rpinfHashCore e.getAppFn
      e.getAppArgs.foldlM (init := h) λ h arg =>
        return mixHash h (← rpinfHashCore arg)
    | .lam _ t b _ | .forallE _ t b _ =>
      return mixHash (← rpinfHashCore t) (← rpinfHashCore b)
    | .letE _ t v b _ =>
      return mixHash (← rpinfHashCore t) $
        mixHash (← rpinfHashCore v) (← rpinfHashCore b)
    | .proj t i e =>
      return mixHash (← rpinfHashCore e) $ mixHash (hash t) (hash i)
    | .mdata d e => if mdataIsProof d then return 13 else rpinfHashCore e
    | .sort .. | .mvar .. | .lit .. | .const .. | .fvar .. | .bvar .. =>
      return e.hash

def rpinfHash (e : Expr) : UInt64 :=
  runST λ _ => rpinfHashCore e |>.run' ∅

structure RPINF where
  expr : Expr
  hash : UInt64
  deriving Inhabited

namespace RPINf

instance : BEq RPINF where
  beq x y := rpinfEq x.expr y.expr

instance : Hashable RPINF where
  hash x := x.hash

instance : ToString RPINF where
  toString r := toString r.expr

instance : ToMessageData RPINF where
  toMessageData r := toMessageData r.expr

end RPINf

structure RPINFCache where
  rpinf : Std.HashMap Expr Expr := ∅
  prop  : Std.HashMap Expr Bool := ∅

abbrev MonadRPINF m := MonadStateOf RPINFCache m

instance [Monad m] [MonadRPINF m] : MonadHashMapCacheAdapter Expr Expr m where
  getCache := return (← getThe RPINFCache).rpinf
  modifyCache f := modifyThe RPINFCache λ s => { s with rpinf := f s.rpinf }

instance [Monad m] [MonadRPINF m] : MonadHashMapCacheAdapter Expr Bool m where
  getCache := return (← getThe RPINFCache).prop
  modifyCache f := modifyThe RPINFCache λ s => { s with prop := f s.prop }

def isPropWithCache [Monad m] [MonadRPINF m] [MonadLiftT MetaM m] (e : Expr) :
    m Bool :=
  checkCache e λ _ => isProp e

def isProofWithCache [Monad m] [MonadRPINF m] [MonadLiftT MetaM m] (e : Expr) :
    m Bool := do
  match (← isProofQuick e) with
  | .true  => return true
  | .false => return false
  | .undef => isPropWithCache (← inferType e)

abbrev RPINFT m [STWorld ω m] := StateRefT RPINFCache m

variable [Monad m] [MonadRPINF m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  [MonadMCtx m] [MonadLiftT (ST IO.RealWorld) m] [MonadError m] [MonadRecDepth m]
  [MonadLiftT BaseIO m]

@[specialize]
partial def pinfCore (statsRef : IO.Ref Nanos) (e : Expr) : m Expr :=
  withIncRecDepth do
  checkCache e λ _ => do
    let (isPrf, nanos) ← time $ isProofWithCache e
    statsRef.modify (· + nanos)
    if isPrf then
      return .mdata (mdataSetIsProof {}) e
    let e ← whnf e
    match e with
    | .app .. =>
        let f ← pinfCore statsRef e.getAppFn'
        let mut args := e.getAppArgs'
        for i in [:args.size] do
          let arg := args[i]!
          args := args.set! i default -- prevent nonlinear access to args[i]
          let arg ← pinfCore statsRef arg
          args := args.set! i arg
        if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
          return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
        else
          return mkAppN f args
    | .lam .. =>
      -- TODO disable cache?
      lambdaTelescope e λ xs e => withNewFVars xs do
        mkLambdaFVars xs (← pinfCore statsRef e)
    | .forallE .. =>
      -- TODO disable cache?
      forallTelescope e λ xs e => withNewFVars xs do
        mkForallFVars xs (← pinfCore statsRef e)
    | .proj t i e =>
      return .proj t i (← pinfCore statsRef e)
    | .sort .. | .mvar .. | .lit .. | .const .. | .fvar .. =>
      return e
    | .letE .. | .mdata .. | .bvar .. => unreachable!
where
  withNewFVars {α} (fvars : Array Expr) (k : m α) : m α := do
    let mut lctx ← (getLCtx : MetaM _)
    for fvar in fvars do
      let fvarId := fvar.fvarId!
      let ldecl ← fvarId.getDecl
      let ldecl := ldecl.setType $ ← pinfCore statsRef ldecl.type
      lctx := lctx.modifyLocalDecl fvarId λ _ => ldecl
    withLCtx lctx (← getLocalInstances) k

def pinf (statsRef : IO.Ref Nanos) (e : Expr) : m Expr := do
  pinfCore statsRef (← instantiateMVars e)

def pinf' (statsRef : IO.Ref Nanos) (e : Expr) : MetaM Expr := do
  (pinfCore statsRef (← instantiateMVars e) : RPINFT MetaM _).run' {}

def rpinfExpr (statsRef : IO.Ref Nanos) (e : Expr) : m Expr :=
  withReducible $ pinf statsRef e

def rpinfExpr' (statsRef : IO.Ref Nanos) (e : Expr) : MetaM Expr :=
  (rpinfExpr statsRef e : RPINFT MetaM _).run' {}

def rpinf (statsRef : IO.Ref Nanos) (e : Expr) : m RPINF := do
  let expr ← rpinfExpr statsRef e
  return { expr, hash := rpinfHash expr }

def rpinf' (statsRef : IO.Ref Nanos) (e : Expr) : MetaM RPINF :=
  (rpinf statsRef e : RPINFT MetaM _).run' {}

end Aesop
