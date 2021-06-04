/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean

-- TODO remove
def as (α : Type _) (a : α) : α := a

notation : min a "@" T => as T a

namespace List

def findAndRemove (P : α → Prop) [DecidablePred P] : List α → Option (α × List α)
  | [] => none
  | (a :: as) =>
    if P a
      then some (a, as)
      else
        match findAndRemove P as with
        | some (x, as) => some (x, a :: as)
        | none => none

section minimumBy

variable (lt : α → α → Prop) [DecidableRel lt]

def minimumBy₁ (a : α) (as : List α) : α :=
  as.foldl (λ a a' => if lt a' a then a' else a) a

def minimumBy : List α → Option α
  | [] => none
  | (a :: as) => some $ minimumBy₁ lt a as

end minimumBy

def minimum' [LT α] [DecidableRel (α := α) (· < ·)] : List α → Option α :=
  minimumBy (· < ·)

def minimum₁ [LT α] [DecidableRel (α := α) (· < ·)] : α → List α → α :=
  minimumBy₁ (· < ·)

end List


namespace Lean.Meta

def conclusionHeadConstant? (e : Expr) : MetaM (Option Name) :=
  forallTelescope e $ λ _ e => e.getAppFn.constName?

end Lean.Meta


namespace Std.Format

def unlines (fs : List Format) : Format :=
  Format.joinSep fs line

end Std.Format


namespace ST.Ref

variable {m} [Monad m] [MonadLiftT (ST σ) m]

@[inline]
unsafe def modifyMUnsafe (r : Ref σ α) (f : α → m α) : m Unit := do
  let v ← r.take
  r.set (← f v)

@[implementedBy modifyMUnsafe]
def modifyM (r : Ref σ α) (f : α → m α) : m Unit := do
  let v ← r.get
  r.set (← f v)

@[inline]
unsafe def modifyGetMUnsafe (r : Ref σ α) (f : α → m (β × α)) : m β := do
  let v ← r.take
  let (b, a) ← f v
  r.set a
  return b

@[implementedBy modifyGetMUnsafe]
def modifyGetM (r : Ref σ α) (f : α → m (β × α)) : m β := do
  let v ← r.get
  let (b, a) ← f v
  r.set a
  return b

end ST.Ref
