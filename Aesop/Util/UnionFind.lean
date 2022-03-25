/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Std

namespace Aesop

open Std (HashMap)

structure UnionFind (α) [BEq α] [Hashable α] where
  parents : Array USize
  sizes : Array USize
  toRep : HashMap α USize
  -- Invariant: `toRep` contains exactly the indices of `parents` as values
  deriving Inhabited

namespace UnionFind

variable {α} [BEq α] [Hashable α]

instance : EmptyCollection (UnionFind α) :=
  ⟨{ parents := #[], sizes := #[], toRep := {} }⟩

def size (u : UnionFind α) : Nat :=
  u.parents.size

def add (x : α) (u : UnionFind α) : UnionFind α := Id.run do
  if u.toRep.contains x then
    return u
  let rep := u.parents.size.toUSize
  { parents := u.parents.push rep
    sizes := u.parents.push 1
    toRep := u.toRep.insert x rep }

def addArray (xs : Array α) (u : UnionFind α) : UnionFind α :=
  xs.foldl (init := u) λ u x => u.add x

def ofArray (xs : Array α) : UnionFind α :=
  ({} : UnionFind α).addArray xs

private unsafe def findRepUnsafe (i : USize) (u : UnionFind α) :
    USize × UnionFind α :=
  let parent := u.parents.uget i lcProof
  if parent == i then
    (parent, u)
  else
    let (parent, u) := u.findRepUnsafe parent
    (parent, { u with parents := u.parents.uset i parent lcProof })

@[implementedBy findRepUnsafe]
private constant findRep : USize → UnionFind α → USize × UnionFind α

partial def find? (x : α) (u : UnionFind α) : Option USize × UnionFind α :=
  match u.toRep.find? x with
  | none => (none, u)
  | some rep =>
    let (rep, u) := u.findRep rep
    (some rep, u)

private unsafe def mergeUnsafe (x y : α) (u : UnionFind α) :
    UnionFind α := Id.run do
  let (some xRep, u) := u.find? x | u
  let (some yRep, u) := u.find? y | u
  if xRep == yRep then
    return u
  else
    let xSize := u.sizes.uget xRep lcProof
    let ySize := u.sizes.uget yRep lcProof
    if xSize < ySize then
      return {
        parents := u.parents.uset xRep yRep lcProof
        sizes := u.sizes.uset yRep (xSize + ySize) lcProof
        toRep := u.toRep
      }
    else
      return {
        parents := u.parents.uset yRep xRep lcProof
        sizes := u.sizes.uset xRep (xSize + ySize) lcProof
        toRep := u.toRep
      }

@[implementedBy mergeUnsafe]
constant merge (x y : α) : UnionFind α → UnionFind α

def sets (u : UnionFind α) : Array (Array α) × UnionFind α :=
  let (sets, u) := u.toRep.fold (init := (HashMap.empty, u)) λ (sets, u) x rep =>
    let (rep, u) := u.findRep rep
    let sets :=
      match sets.find? rep with
      | some set => sets.insert rep (set.push x)
      | none => sets.insert rep #[x]
    (sets, u)
  let sets := sets.fold (init := Array.mkEmpty sets.size) λ sets _ v =>
    sets.push v
  (sets, u)

end Aesop.UnionFind
