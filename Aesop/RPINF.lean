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

namespace PIHashM

structure State where
  cache : Std.HashMap USize UInt64 := ∅
  tempFVars : Std.HashSet FVarId := ∅
  deriving Inhabited

end PIHashM

abbrev PIHashM := StateRefT PIHashM.State MetaM

instance : MonadHashMapCacheAdapter USize UInt64 PIHashM where
  getCache := return (← get).cache
  modifyCache f := modify λ s => { s with cache := f s.cache }

partial def piHashCore (e : Expr) : PIHashM UInt64 :=
  withIncRecDepth do
  checkCache (unsafe ptrAddrUnsafe e) λ _ => do
    if ← isProof e then
      return 7
    match e with
    | .fvar fvarId =>
      if (← get).tempFVars.contains fvarId then
        return 13
      else
        return e.hash
    | .app .. =>
      let h ← piHashCore e.getAppFn
      e.getAppArgs.foldlM (init := h) λ h arg =>
        return mixHash h (← piHashCore arg)
    | .lam .. => lambdaTelescope e λ xs e => hashBinders xs e
    | .forallE .. => forallTelescope e λ xs e => hashBinders xs e
    | .letE .. => lambdaLetTelescope e λ xs e => hashBinders xs e
    | .proj t i e =>
      return mixHash (← piHashCore e) $ mixHash (hash t) (hash i)
    | .mdata _ e => piHashCore e
    | .bvar .. => unreachable!
    | .sort .. | .mvar .. | .lit .. | .const .. =>
      return e.hash
where
  hashBinders (fvars : Array Expr) (body : Expr) :
      PIHashM UInt64 := do
    modify λ s => {
      s with
      tempFVars :=
        fvars.foldl (init := s.tempFVars) λ tempFVars fvar =>
          tempFVars.insert fvar.fvarId!
    }
    let h ← piHashCore body
    fvars.foldlM (init := h) λ h fvar => do
      let ldecl ← fvar.fvarId!.getDecl
      let typeHash ← piHashCore ldecl.type
      let ldeclHash ← do
        match ldecl.value? with
        | none => pure typeHash
        | some val => pure $ mixHash typeHash (← piHashCore val)
      return mixHash h ldeclHash

def piHash (e : Expr) : MetaM UInt64 :=
  piHashCore e |>.run' {}

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

protected def ofRPINFExpr (e : Expr) : MetaM RPINF :=
  return { expr := e, hash := ← piHash e }

end RPINf

class abbrev MonadRPINF (m : Type → Type) :=
  MonadCache Expr RPINF m

variable [Monad m] [MonadRPINF m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
  [MonadMCtx m] [MonadLiftT (ST IO.RealWorld) m] [MonadError m] [MonadRecDepth m]

local instance : STWorld IO.RealWorld m where

@[specialize]
partial def rpinfCore (e : Expr) : StateRefT FVarIdHashSet m RPINF :=
  have : MonadCache Expr RPINF (StateRefT FVarIdHashSet m) := {
    findCached? := λ x => (MonadCache.findCached? x : m _)
    cache := λ a b => (MonadCache.cache a b : m _)
  }
  have : AddErrorMessageContext (StateRefT FVarIdHashSet m) := {
    add := λ ref msg => (AddErrorMessageContext.add ref msg : m _)
  }
  withIncRecDepth do
  checkCache e λ _ => do
    if ← isProof e then
      let e := .mdata (mdataSetIsProof {}) e
      return { expr := e, hash := 7 }
    let e ← whnf e
    match e with
    | .fvar fvarId =>
      if (← get).contains fvarId then
        -- All fvars that were earlier substituted for bound variables are hashed
        -- to the same value. This is needed to ensure that the arbitrarily
        -- chosen FVarId doesn't matter.
        return { expr := e, hash := 13 }
      else
        return { expr := e, hash := e.hash }
    | .app f e =>
        let { expr := f, hash := h } ← rpinfCore f
        let mut h := h
        let mut args := e.getAppArgs
        for i in [:args.size] do
          let arg := args[i]!
          args := args.set! i default -- prevent nonlinear access to arg
          let { expr := arg, hash := argHash } ← rpinfCore arg
          args := args.set! i arg
          h := mixHash h argHash
        if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
          let e := mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
          return { expr := e, hash := e.hash }
        else
          return { expr := mkAppN f args, hash := h }
    | .lam .. =>
      -- TODO disable cache?
      lambdaTelescope e λ xs e => do
        let r ← hashBinders xs e
        return { r with expr := ← mkLambdaFVars xs e }
    | .forallE .. =>
      -- TODO disable cache?
      forallTelescope e λ xs e => do
        let r ← hashBinders xs e
        return { r with expr := ← mkForallFVars xs e }
    | .proj t i e =>
      let { expr := e, hash := h } ← rpinfCore e
      let e := .proj t i e
      let h := mixHash h $ mixHash (hash t) (hash i)
      return { expr := e, hash := h }
    | .sort .. | .mvar .. | .lit .. | .const .. =>
      return { expr := e, hash := e.hash }
    | .letE .. | .mdata .. | .bvar .. => unreachable!
where
  hashBinders (fvars : Array Expr) (body : Expr) :
      StateRefT FVarIdHashSet m RPINF := do
    modify λ s => fvars.foldl (init := s) λ s fvar => s.insert fvar.fvarId!
    let { expr := e, hash := h } ← rpinfCore body
    let h ← fvars.foldlM (init := h) λ h fvar =>
      return mixHash h (← rpinfCore $ ← fvar.fvarId!.getType).hash
    return { expr := e, hash := h }

def rpinf (e : Expr) : m RPINF :=
  withReducible do rpinfCore (← instantiateMVars e) |>.run' ∅

def rpinf' (e : Expr) : MetaM RPINF :=
  (rpinf e : MonadCacheT Expr RPINF MetaM _).run

end Aesop
