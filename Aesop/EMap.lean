/-
Copyright (c) 2025 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

module

public import Aesop.Tracing

public section

open Lean Lean.Meta

namespace Aesop

/-- A map whose keys are expressions. Keys are identified up to defeq. We use
`reducible` transparency and treat metavariables as rigid (i.e.,
unassignable). -/
structure EMap (α) where
  rep : AssocList Expr α
  deriving Inhabited

namespace EMap

protected def empty : EMap α :=
  ⟨.nil⟩

instance : EmptyCollection (EMap α) :=
  ⟨.empty⟩

variable [Monad m] [MonadLiftT MetaM m]

instance : ForM m (EMap α) (Expr × α) where
  forM map f := map.rep.forM fun e a => f (e, a)

instance : ForIn m (EMap α) (Expr × α) where
  forIn map := map.rep.forIn

def foldlM (init : σ) (f : σ → Expr → α → m σ) (map : EMap α) : m σ :=
  map.rep.foldlM f init

def foldl (init : σ) (f : σ → Expr → α → σ) (map : EMap α) : σ :=
  map.rep.foldl f init

private def isDefEqEMap (s t : Expr) : MetaM Bool := do
  withAesopTraceNode .forwardDebug (fun r => return m!"{exceptBoolEmoji r} {s} ≟ {t}") do
  withNewMCtxDepth do
  withReducible do
    isDefEq s t

def alterM (e : Expr) (f : α → m (Option α × β)) (map : EMap α) :
    m (EMap α × Option β) := do
  let lctx ← show MetaM _ from getLCtx
  let (map, b?) ← go lctx map.rep
  return (⟨map⟩, b?)
where
  go (lctx : LocalContext) : AssocList Expr α → m (AssocList Expr α × Option β)
    | .nil => return (.nil, none)
    | .cons e' old map => do
      if e'.hasAnyFVar (! lctx.contains ·) then
        return ← go lctx map
      if ← isDefEqEMap e' e then
        let (new?, b) ← f old
        match new? with
        | none =>     return (map, b)
        | some new => return (.cons e' new map, b)
      else
        let (map, b) ← go lctx map
        return (.cons e' old map, b)

def alter (e : Expr) (f : α → Option α × β) (map : EMap α) :
    MetaM (EMap α × Option β) := do
  inline map.alterM e fun a => return f a

def insertNew (e : Expr) (a : α) (map : EMap α) : EMap α :=
  ⟨.cons e a map.rep⟩

def insertWithM (e : Expr) (f : Option α → m α) (map : EMap α) :
    m (EMap α × Option α × α) := do
  let (map, vals?) ← map.alterM e fun old => do
    let new ← f (some old)
    return (new, (old, new))
  match vals? with
  | none =>
    let new ← f none
    return (⟨.cons e new map.rep⟩, none, new)
  | some (old, new) =>
    return (map, old, new)

def insertWith (e : Expr) (f : Option α → α) (map : EMap α) :
    MetaM (EMap α × Option α × α) :=
  inline map.insertWithM e fun a? => return f a?

def insert (e : Expr) (a : α) (map : EMap α) : MetaM (EMap α) :=
  inline (·.fst) <$> map.insertWithM e (fun _ => return a)

def singleton (e : Expr) (a : α) : EMap α :=
  ⟨.cons e a .nil⟩

def findWithKey? (e : Expr) (map : EMap α) : MetaM (Option (Expr × α)) := do
  let lctx ← getLCtx
  for (e', a) in map.rep do
    if e'.hasAnyFVar (! lctx.contains ·) then
      continue
    if ← isDefEqEMap e e' then
      return some (e', a)
  return none

def find? (e : Expr) (map : EMap α) : MetaM (Option α) := do
  return (← inline map.findWithKey? e).map (·.2)

private def mapMAssocList (f : α → β → m γ) : AssocList α β → m (AssocList α γ)
  | .nil => return .nil
  | .cons a b xs => return (.cons a (← f a b) (← mapMAssocList f xs))

def mapM (f : Expr → α → m β) (map : EMap α) : m (EMap β) :=
  return ⟨← inline mapMAssocList f map.rep⟩

def map (f : Expr → α → β) (map : EMap α) : EMap β :=
  map.mapM (m := Id) f

end EMap
end Aesop
