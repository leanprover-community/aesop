/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Nanos
import Aesop.Util.UnionFind
import Std.Data.Prod.Lex
import Std.Lean.Expr
import Std.Lean.HashSet
import Std.Lean.Meta.InstantiateMVars
import Std.Lean.Meta.DiscrTree


def BEq.ofOrd (ord : Ord α) : BEq α where
  beq x y :=
    match ord.compare x y with
    | Ordering.eq => true
    | _ => false

namespace Ordering

def isEQ : Ordering → Bool
  | eq => true
  | _ => false

def opposite : Ordering → Ordering
  | lt => gt
  | eq => eq
  | gt => lt

end Ordering


@[inline]
def compareLexicographic (cmp₁ : α → α → Ordering) (cmp₂ : α → α → Ordering)
    (x y : α) : Ordering :=
  match cmp₁ x y with
  | Ordering.eq => cmp₂ x y
  | ord => ord

@[inline]
def compareOpposite (cmp : α → α → Ordering) (x y : α) : Ordering :=
  cmp x y |>.opposite


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


namespace Array


set_option linter.unusedVariables false in
def mergeSortedFilteringDuplicates [ord : Ord α] (xs ys : Array α) :
    Array α :=
  mergeSortedMergingDuplicates xs ys λ x _ => x

-- Merge `xs` and `ys`, which do not need to be sorted. Elements which occur in
-- both `xs` and `ys` are only added once. If `xs` and `ys` do not contain
-- duplicates, then neither does the result. O(n*m)!
set_option linter.unusedVariables false in
def mergeUnsortedFilteringDuplicates [eq : BEq α] (xs ys : Array α) :
    Array α :=
  -- Ideally we would check whether `xs` or `ys` have spare capacity, to prevent
  -- copying if possible. But Lean arrays don't expose their capacity.
  if xs.size < ys.size then go ys xs else go xs ys
  where
    @[inline]
    go (xs ys : Array α) :=
      let xsSize := xs.size
      ys.foldl (init := xs) λ xs y =>
        if xs[:xsSize].contains y then xs else xs.push y

set_option linter.unusedVariables false in
def deduplicate [Inhabited α] [BEq α] [ord : Ord α] (xs : Array α) : Array α :=
  deduplicateSorted $ xs.qsort λ x y => compare x y |>.isLT

set_option linter.unusedVariables false in
@[inline]
protected def max [ord : Ord α] [Inhabited α] (xs : Array α) (start := 0)
    (stop := xs.size) : α :=
  xs.maxD default start stop

set_option linter.unusedVariables false in
@[inline]
protected def min [ord : Ord α] [Inhabited α] (xs : Array α) (start := 0)
    (stop := xs.size) : α :=
  xs.minD default start stop

end Array


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


namespace Lean.Expr

def arity : Expr → Nat
  | forallE _ _ body _ => 1 + arity body
  | _ => 0

end Lean.Expr


namespace Lean.MessageData

def joinSepArray (ms : Array MessageData) (sep : MessageData) :
    MessageData := Id.run do
  let mut result := nil
  let last := ms.size - 1
  for h : i in [0:ms.size] do
    if i ≥ last then
      result := result ++ ms[i]'h.2
    else
      result := result ++ ms[i]'h.2 ++ sep
  return result

@[inline]
def unlines (ms : Array MessageData) : MessageData :=
  joinSepArray ms Format.line

-- TODO this is for compatibility with a previous version of the MessageData
-- API.
def node (fs : Array MessageData) : MessageData :=
  indentD (unlines fs)

def nodeFiltering (fs : Array (Option MessageData)) : MessageData :=
  node $ fs.filterMap id

end Lean.MessageData


namespace Std.HashMap

variable [BEq α] [Hashable α]

def merge (m n : HashMap α β) (f : α → β → β → β) : HashMap α β :=
  if m.size < n.size then loop m n else loop n m
  where
    @[inline]
    loop m n :=
      m.fold (init := n) λ map k v =>
        match map.find? k with
        | none => map.insert k v
        | some v' => map.insert k $ f k v v'

instance : ForIn m (HashMap α β) (α × β) where
  forIn m init f := do
    let mut acc := init
    for buckets in m.val.buckets.val do
      for d in buckets do
        match ← f d acc with
        | .done b => return b
        | .yield b => acc := b
    return acc

end Std.HashMap


namespace Lean.PersistentHashSet

@[inline]
def merge [BEq α] [Hashable α] (s t : PersistentHashSet α) :
    PersistentHashSet α :=
  if s.size < t.size then loop s t else loop t s
  where
    @[inline]
    loop s t := s.fold (init := t) λ s a => s.insert a

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


namespace Lean.PersistentHashMap

variable [BEq α] [Hashable α]

def merge (m n : PersistentHashMap α β) (f : α → β → β → β) :
    PersistentHashMap α β :=
  if m.size < n.size then loop m n f else loop n m (λ a b b' => f a b' b)
  where
    @[inline]
    loop m n f := m.foldl (init := n) λ map k v =>
      match map.find? k with
      | none => map.insert k v
      | some v' => map.insert k $ f k v v'

end Lean.PersistentHashMap


namespace Lean.Meta.DiscrTree

namespace Trie

partial def merge : Trie α s → Trie α s → Trie α s
  | node vs₁ cs₁, node vs₂ cs₂ =>
    node (mergeValues vs₁ vs₂) (mergeChildren cs₁ cs₂)
  where
    mergeValues (vs₁ vs₂ : Array α) : Array α :=
      if vs₁.size > vs₂.size then vs₁ ++ vs₂ else vs₂ ++ vs₁

    mergeChildren (cs₁ cs₂ : Array (Key s × Trie α s)) :
        Array (Key s × Trie α s) :=
      Array.mergeSortedMergingDuplicates
        (ord := ⟨λ (k₁, _) (k₂, _) => compare k₁ k₂⟩) cs₁ cs₂
        (λ (k₁, t₁) (_, t₂) => (k₁, merge t₁ t₂))

end Trie

@[inline]
def merge [BEq α] (t u : DiscrTree α s) : DiscrTree α s :=
  { root := t.root.merge u.root λ _ trie₁ trie₂ => trie₁.merge trie₂ }

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
  let arity := info.type.arity
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
    pre := s.pre.merge t.pre
    post := s.post.merge t.post
    lemmaNames := s.lemmaNames.merge t.lemmaNames
    toUnfold := s.toUnfold.merge t.toUnfold
    toUnfoldThms := s.toUnfoldThms.merge t.toUnfoldThms
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

open MessageData in
protected def toMessageData (s : SimpTheorems) : MessageData :=
  node #[
    "pre lemmas:" ++ node (s.pre.values.map toMessageData),
    "post lemmas:" ++ node (s.post.values.map toMessageData),
    "definitions to unfold:" ++ node
      (s.toUnfold.toArray.qsort Name.lt |>.map toMessageData),
    "erased entries:" ++ node
      (s.erased.toArray.qsort (λ o₁ o₂ => o₁.key.lt o₂.key) |>.map (·.key))
  ]

end Lean.Meta.SimpTheorems

namespace Lean.Meta

def matchAppOf (f : Expr) (e : Expr) : MetaM (Option (Array Expr)) := do
  let type ← inferType f
  let (mvars, _, _) ← forallMetaTelescope type
  let app := mkAppN f mvars
  if ← isDefEq app e then
    some <$> mvars.mapM instantiateMVars
  else
    return none

end Lean.Meta


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
