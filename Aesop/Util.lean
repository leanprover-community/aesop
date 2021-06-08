/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean
import Std.Data.BinomialHeap

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


namespace Std.PersistentHashSet

@[inline]
def merge [BEq α] [Hashable α] (s t : PersistentHashSet α) : PersistentHashSet α :=
  if s.size < t.size then loop s t else loop t s
  where
    @[inline]
    loop s t := s.fold (init := t) λ s a => s.insert a

end Std.PersistentHashSet


namespace Std.PersistentHashMap

@[inline]
def merge [BEq α] [Hashable α] (m n : PersistentHashMap α β) (f : α → β → β → β) :
    PersistentHashMap α β :=
  if m.size < n.size then loop m n f else loop n m (λ a b b' => f a b' b)
  where
    @[inline]
    loop m n f := m.foldl (init := n) λ map k v =>
      match map.find? k with
      | some v' => map.insert k (f k v v')
      | none => map.insert k v

end Std.PersistentHashMap


namespace Lean.Meta

-- TODO unused?
def conclusionHeadConstant? (e : Expr) : MetaM (Option Name) :=
  forallTelescope e $ λ _ e => e.getAppFn.constName?

def copyMVar (mvarId : MVarId) : MetaM MVarId := do
  let decl ← getMVarDecl mvarId
  let mv ← mkFreshExprMVarAt decl.lctx decl.localInstances decl.type decl.kind
    decl.userName decl.numScopeArgs
  return mv.mvarId!

namespace DiscrTree.Trie

unsafe def foldMUnsafe [Monad m] (initialKeys : Array Key)
    (f : σ → Array Key → α → m σ) (init : σ) : Trie α → m σ
  | Trie.node vs children => do
    let s ← vs.foldlM (init := init) λ s v => f s initialKeys v
    children.foldlM (init := s) λ s (k, t) =>
      t.foldMUnsafe (initialKeys.push k) f s

@[implementedBy foldMUnsafe]
constant foldM [Monad m] (initalKeys : Array Key)
    (f : σ → Array Key → α → m σ) (init : σ) (t : Trie α) : m σ :=
  pure init

@[inline]
def fold (initialKeys : Array Key) (f : σ → Array Key → α → σ) (init : σ)
    (t : Trie α) : σ :=
  Id.run $ foldM initialKeys (λ s k a => return f s k a) init t

end Trie

@[inline]
def foldM [Monad m] (f : σ → Array Key → α → m σ) (init : σ) (t : DiscrTree α) :
    m σ :=
  t.root.foldlM (init := init) λ s k t => t.foldM #[k] (init := s) f

@[inline]
def fold (f : σ → Array Key → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run $ foldM (λ s keys a => return f s keys a) init t

-- TODO inefficient since it doesn't take advantage of the Trie structure at all
@[inline]
def merge [BEq α] (t u : DiscrTree α) : DiscrTree α :=
  if t.root.size < u.root.size then loop t u else loop u t
  where
    loop t u := t.fold (init := u) λ u keys a => DiscrTree.insertCore u keys a

end DiscrTree

namespace SimpLemmas

def merge (s t : SimpLemmas) : SimpLemmas where
  pre := s.pre.merge t.pre
  post := s.post.merge t.post
  lemmaNames := s.lemmaNames.merge t.lemmaNames
  toUnfold := s.toUnfold.merge t.toUnfold
  erased := s.erased.merge t.erased

end SimpLemmas

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


namespace Std.BinomialHeap

@[inline]
def removeMin {lt : α → α → Bool} (h : BinomialHeap α lt) :
    Option (α × BinomialHeap α lt) :=
  match h.head? with
  | some hd => some (hd, h.tail)
  | none => none

end Std.BinomialHeap


namespace MonadStateOf

@[inline]
def ofLens [Monad m] [MonadStateOf α m] (project : α → β) (inject : β → α → α) :
    MonadStateOf β m where
  get := return project (← get)
  set b := modify λ a => inject b a
  modifyGet f := modifyGet λ a =>
    let (r, b) := f (project a)
    (r, inject b a)

end MonadStateOf

@[inline]
abbrev setThe (σ) {m} [MonadStateOf σ m] (s : σ) : m PUnit :=
  MonadStateOf.set s
