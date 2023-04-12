/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Nanos
import Aesop.Util.UnionFind
import Std.Lean.Expr
import Std.Lean.Meta.DiscrTree
import Std.Lean.PersistentHashSet


namespace Subarray

def popFront? (as : Subarray α) : Option (α × Subarray α) :=
  if h : as.start < as.stop
    then
      let head := as.as.get ⟨as.start, Nat.lt_of_lt_of_le h as.h₂⟩
      let tail :=
        { as with
          start := as.start + 1
          h₁ := Nat.le_of_lt_succ $ Nat.succ_lt_succ h  }
      some (head, tail)
    else
      none

end Subarray


namespace IO

@[inline]
def time [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Aesop.Nanos) := do
  let start ← monoNanosNow
  let a ← x
  let stop ← monoNanosNow
  return (a, ⟨stop - start⟩)

@[inline]
def time' [Monad m] [MonadLiftT BaseIO m] (x : m Unit) : m Aesop.Nanos := do
  let start ← monoNanosNow
  x
  let stop ← monoNanosNow
  return ⟨stop - start⟩

end IO


namespace Lean.PersistentHashSet

-- Elements are returned in unspecified order.
@[inline]
def toList [BEq α] [Hashable α] (s : PersistentHashSet α) : List α :=
  s.fold (init := []) λ as a => a :: as

-- Elements are returned in unspecified order. (In fact, they are currently
-- returned in reverse order of `toList`.)
@[inline]
def toArray [BEq α] [Hashable α] (s : PersistentHashSet α) : Array α :=
  s.fold (init := Array.mkEmpty s.size) λ as a => as.push a

end Lean.PersistentHashSet


namespace Lean.Meta.DiscrTree

-- For `type = ∀ (x₁, ..., xₙ), T`, returns keys that match `T * ... *` (with
-- `n` stars).
def getConclusionKeys (type : Expr) :
    MetaM (Array (Key s)) :=
  withoutModifyingState do
    let (_, _, conclusion) ← forallMetaTelescope type
    mkPath conclusion
    -- We use a meta telescope because `DiscrTree.mkPath` ignores metas (they
    -- turn into `Key.star`) but not fvars.

-- For a constant `d` with type `∀ (x₁, ..., xₙ), T`, returns keys that
-- match `d * ... *` (with `n` stars).
def getConstKeys (decl : Name) : MetaM (Array (Key s)) := do
  let (some info) ← getConst? decl
    | throwUnknownConstant decl
  let arity := info.type.forallArity
  let mut keys := Array.mkEmpty (arity + 1)
  keys := keys.push $ .const decl arity
  for _ in [0:arity] do
    keys := keys.push $ .star
  return keys

end Lean.Meta.DiscrTree


namespace Lean.Meta.SimpTheorems

def addSimpEntry (s : SimpTheorems) : SimpEntry → SimpTheorems
  | SimpEntry.thm l =>
    { addSimpTheoremEntry s l with erased := s.erased.erase l.origin }
  | SimpEntry.toUnfold d =>
    { s with toUnfold := s.toUnfold.insert d }
  | SimpEntry.toUnfoldThms n thms => s.registerDeclToUnfoldThms n thms

def eraseSimpEntry (s : SimpTheorems) : SimpEntry → SimpTheorems
  | SimpEntry.thm l =>
    let o := l.origin
    { s with erased := s.erased.insert o, lemmaNames := s.lemmaNames.erase o }
  | SimpEntry.toUnfold d =>
    { s with toUnfold := s.toUnfold.erase d }
  | SimpEntry.toUnfoldThms n _ =>
    { s with toUnfoldThms := s.toUnfoldThms.erase n }

def foldSimpEntriesM [Monad m] (f : σ → SimpEntry → m σ) (init : σ)
    (thms : SimpTheorems) : m σ := do
  let s ← thms.pre.foldValuesM  (init := init) processTheorem
  let s ← thms.post.foldValuesM (init := s)    processTheorem
  let s ← thms.toUnfold.foldM (init := s) λ s n => f s (SimpEntry.toUnfold n)
  thms.toUnfoldThms.foldlM (init := s) λ s n thms =>
    f s (SimpEntry.toUnfoldThms n thms)
  where
    @[inline]
    processTheorem (s : σ) (thm : SimpTheorem) : m σ :=
      if thms.erased.contains thm.origin then
        return s
      else
        f s (SimpEntry.thm thm)

def foldSimpEntries (f : σ → SimpEntry → σ) (init : σ) (thms : SimpTheorems) :
    σ :=
  Id.run $ foldSimpEntriesM f init thms

def simpEntries (thms : SimpTheorems) : Array SimpEntry :=
  thms.foldSimpEntries (init := #[]) λ s thm => s.push thm

def merge (s t : SimpTheorems) : SimpTheorems := {
    pre := s.pre.mergePreservingDuplicates t.pre
    post := s.post.mergePreservingDuplicates t.post
    lemmaNames := s.lemmaNames.merge t.lemmaNames
    toUnfold := s.toUnfold.merge t.toUnfold
    toUnfoldThms := s.toUnfoldThms.mergeWith t.toUnfoldThms
      (λ _ thms₁ _ => thms₁)
      -- We can ignore collisions here because the theorems should always be the
      -- same.
    erased := mkErased t s $ mkErased s t {}
  }
  where
    -- Adds the erased lemmas from `s` to `init`, excluding those lemmas which
    -- occur in `t`.
    mkErased (s t : SimpTheorems) (init : PHashSet Origin) : PHashSet Origin :=
      s.erased.fold (init := init) λ x origin =>
        -- I think the following check suffices to ensure that `decl` does not
        -- occur in `t`. If `decl` is an unfold theorem (in the sense of
        -- `toUnfoldThms`), then it occurs also in `t.lemmaNames`.
        if t.lemmaNames.contains origin || t.toUnfold.contains origin.key then
          x
        else
          x.insert origin

end Lean.Meta.SimpTheorems


@[inline]
def setThe (σ) {m} [MonadStateOf σ m] (s : σ) : m PUnit :=
  MonadStateOf.set s


namespace Lean

@[inline]
def runMetaMAsCoreM (x : MetaM α) : CoreM α :=
  Prod.fst <$> x.run {} {}

@[inline]
def runTermElabMAsCoreM (x : Elab.TermElabM α) : CoreM α :=
  runMetaMAsCoreM x.run'

end Lean


namespace Aesop

open Lean Lean.Meta

def isAppOfUpToDefeq (f : Expr) (e : Expr) : MetaM Bool :=
  withoutModifyingState do
    let type ← inferType f
    let (mvars, _, _) ← forallMetaTelescope type
    let app := mkAppN f mvars
    if ← isDefEq app e then
      return true
    else
      return false

section TransparencySyntax

def withTransparencySyntax [Monad m] [MonadQuotation m] (md : TransparencyMode)
    (k : TSyntax `tactic) : m (TSyntax `tactic) :=
  match md with
  | .default   => return k
  | .all       => `(tactic| with_unfolding_all $k:tactic)
  | .reducible => `(tactic| with_reducible $k:tactic)
  | .instances => `(tactic| with_reducible_and_instances $k:tactic)

def withAllTransparencySyntax [Monad m] [MonadQuotation m]
    (md : TransparencyMode) (k : TSyntax `tactic) :
    m (TSyntax `tactic) :=
  match md with
  | .all  => `(tactic| with_unfolding_all $k:tactic)
  | _     => return k

end TransparencySyntax

/--
If the input expression `e` reduces to `f x₁ ... xₙ` via repeated `whnf`, this
function returns `f` and `[x₁, ⋯, xₙ]`. Otherwise it returns `e` (unchanged, not
in WHNF!) and `[]`.
-/
partial def getAppUpToDefeq (e : Expr) : MetaM (Expr × Array Expr) :=
  go #[] e
where
  go (args : Array Expr) (e : Expr) : MetaM (Expr × Array Expr) := do
    match ← whnf e with
    | .app f e => go (args.push e) f
    | _ => return (e, args.reverse)

section DiscrTree

open DiscrTree

def isEmptyTrie : Trie α s → Bool
  | .node vs children => vs.isEmpty && children.isEmpty

private partial def filterTrie (removed : Array (Array (Key s) × α))
    (parentKeys : Array (Key s)) (p : α → Bool) :
    Trie α s → Trie α s × Array (Array (Key s) × α)
  | .node vs children =>
    let (vs, removed') := vs.partition p
    let removed := removed ++ removed'.map (λ v => (parentKeys, v))
    let (children, removed) := go removed 0 children
    let children := children.filter λ (_, c) => ! isEmptyTrie c
    (.node vs children, removed)
  where
    go (removed : Array (Array (Key s) × α)) (i : Nat)
        (children : Array (Key s × Trie α s)) :
        Array (Key s × Trie α s) × Array (Array (Key s) × α) :=
      if h : i < children.size then
        let (key, t) := children[i]'h
        let (t, removed') := filterTrie removed (parentKeys.push key) p t
        go (removed ++ removed') (i + 1) (children.set ⟨i, h⟩ (key, t))
      else
        (children, removed)

def filterDiscrTreeCore (t : DiscrTree α s)
    (removed : Array (Array (Key s) × α)) (p : α → Bool) :
    DiscrTree α s × Array (Array (Key s) × α) :=
  let (root, removed) :=
    t.root.foldl (init := (.empty, removed)) λ (root, removed) key t =>
      let (t, removed') := filterTrie removed #[key] p t
      let root := if isEmptyTrie t then root else root.insert key t
      (root, removed ++ removed')
  (⟨root⟩, removed)

/--
Remove elements for which `p` returns `false` from the given `DiscrTree`. The
modified `DiscrTree` is returned along with the removed elements.
-/
def filterDiscrTree (t : DiscrTree α s) (p : α → Bool) :
    DiscrTree α s × Array (Array (Key s) × α) :=
  filterDiscrTreeCore t #[] p

end Aesop.DiscrTree
