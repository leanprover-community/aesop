/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- `MData` tag for expressions that are proofs. -/
def mdataPINFIsProofName : Name :=
  `Aesop.pinfIsProof

/-- Modify `d` to indicate that the enclosed expression is a proof. -/
def mdataSetIsProof (d : MData) : MData :=
  d.insert mdataPINFIsProofName true

/-- Check whether `d` indicates that the enclosed expression is a proof. -/
def mdataIsProof (d : MData) : Bool :=
  d.getBool mdataPINFIsProofName (defVal := false)

mutual
  /-- Check whether two expressions in PINF are equal. We assume that the two
  expressions are type-correct, in PINF and have defeq types. -/
  def pinfEqCore : (x y : Expr) → Bool
    | .bvar i₁, .bvar i₂ => i₁ == i₂
    | .fvar id₁, .fvar id₂ => id₁ == id₂
    | .mvar id₁, .mvar id₂ => id₁ == id₂
    | .sort u, .sort v => u == v
    | .const n₁ us, .const n₂ vs => n₁ == n₂ && us == vs
    | .app f₁ e₁, .app f₂ e₂ => pinfEq f₁ f₂ && pinfEq e₁ e₂
    | .lam _ t₁ e₁ bi₁, .lam _ t₂ e₂ bi₂ =>
      bi₁ == bi₂ && pinfEq t₁ t₂ && pinfEq e₁ e₂
    | .forallE _ t₁ e₁ bi₁, .forallE _ t₂ e₂ bi₂ =>
      bi₁ == bi₂ && pinfEq t₁ t₂ && pinfEq e₁ e₂
    | .letE _ t₁ v₁ e₁ _, .letE _ t₂ v₂ e₂ _ =>
      pinfEq v₁ v₂ && pinfEq t₁ t₂ && pinfEq e₁ e₂
    | .lit l₁, .lit l₂ => l₁ == l₂
    | .mdata d e₁, e₂ | e₁, .mdata d e₂ => mdataIsProof d || pinfEq e₁ e₂
    | _, _ => false

  @[inherit_doc pinfEqCore]
  def pinfEq (x y : Expr) : Bool :=
    (unsafe ptrEq x y) || pinfEqCore x y
end

/-- Compute the PINF hash of an expression in PINF. The hash ignores binder
names, binder info and proofs marked by `mdataPINFIsProofName`. -/
partial def pinfHashCore (e : Expr) :
    StateRefT (Std.HashMap UInt64 UInt64) (ST s) UInt64 :=
  have : MonadHashMapCacheAdapter UInt64 UInt64
           (StateRefT (Std.HashMap UInt64 UInt64) (ST s)) := {
    getCache := get
    modifyCache := modify
  }
  checkCache e.hash λ _ => do
    match e with
    | .app .. =>
      let h ← pinfHashCore e.getAppFn
      e.getAppArgs.foldlM (init := h) λ h arg =>
        return mixHash h (← pinfHashCore arg)
    | .lam _ t b _ | .forallE _ t b _ =>
      return mixHash (← pinfHashCore t) (← pinfHashCore b)
    | .letE _ t v b _ =>
      return mixHash (← pinfHashCore t) $
        mixHash (← pinfHashCore v) (← pinfHashCore b)
    | .proj t i e =>
      return mixHash (← pinfHashCore e) $ mixHash (hash t) (hash i)
    | .mdata d e => if mdataIsProof d then return 13 else pinfHashCore e
    | .sort .. | .mvar .. | .lit .. | .const .. | .fvar .. | .bvar .. =>
      return e.hash

@[inherit_doc pinfHashCore]
def pinfHash (e : Expr) : UInt64 :=
  runST λ _ => pinfHashCore e |>.run' ∅

set_option linter.missingDocs false in
/-- An expression in PINF at transparency `md`. -/
structure PINFRaw (md : TransparencyMode) where
  toExpr : Expr
  deriving Inhabited

instance : BEq (PINFRaw md) where
  beq x y := pinfEq x.toExpr y.toExpr

instance : Hashable (PINFRaw md) where
  hash x := pinfHash x.toExpr

instance : ToString (PINFRaw md) where
  toString x := toString x.toExpr

instance : ToFormat (PINFRaw md) where
  format x := format x.toExpr

instance : ToMessageData (PINFRaw md) where
  toMessageData x := toMessageData x.toExpr

/-- An expression in PINF at `reducible` transparency. -/
abbrev RPINFRaw := PINFRaw .reducible

set_option linter.missingDocs false in
/-- Cache for `rpinf`. -/
structure RPINFCache where
  map : Std.HashMap Expr RPINFRaw
  deriving Inhabited

instance : EmptyCollection RPINFCache :=
  ⟨⟨∅⟩⟩

set_option linter.missingDocs false in
/-- An expression in PINF at transparency `md`, together with its PINF hash as
computed by `pinfHash`. -/
structure PINF (md : TransparencyMode) where
  toExpr : Expr
  hash : UInt64
  deriving Inhabited

instance : BEq (PINF md) where
  beq x y := pinfEq x.toExpr y.toExpr

instance : Hashable (PINF md) where
  hash x := x.hash

instance : Ord (PINF md) where
  compare x y :=
    if x == y then .eq else if x.toExpr.lt y.toExpr then .lt else .gt

instance : ToString (PINF md) where
  toString x := toString x.toExpr

instance : ToFormat (PINF md) where
  format x := format x.toExpr

instance : ToMessageData (PINF md) where
  toMessageData x := toMessageData x.toExpr

/-- An expression in RPINF together with its RPINF hash. -/
abbrev RPINF := PINF .reducible

end Aesop
