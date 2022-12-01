/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Nanos
import Aesop.Util.UnionFind
import Lean
import Std


def BEq.ofOrd (ord : Ord α) : BEq α where
  beq x y :=
    match ord.compare x y with
    | Ordering.eq => true
    | _ => false

instance (priority := low) [ord : Ord α] : BEq α :=
  BEq.ofOrd ord


namespace Option

def toArray : Option α → Array α
  | none => #[]
  | some a => #[a]

def forM [Monad m] (f : α → m Unit) : Option α → m Unit
  | none => pure ()
  | some a => f a

end Option

namespace Ordering

def isLT : Ordering → Bool
  | lt => true
  | _ => false

def isEQ : Ordering → Bool
  | eq => true
  | _ => false

def isGT : Ordering → Bool
  | gt => true
  | _ => false

def isGE : Ordering → Bool
  | lt => false
  | eq => true
  | gt => true

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
def compareOn [ord : Ord β] (f : α → β) (x y : α) : Ordering :=
  compare (f x) (f y)

@[inline]
def compareOpposite (cmp : α → α → Ordering) (x y : α) : Ordering :=
  cmp x y |>.opposite


namespace Subarray

protected def empty : Subarray α where
  as := #[]
  start := 0
  stop := 0
  h₁ := Nat.le_refl 0
  h₂ := Nat.le_refl 0

instance : EmptyCollection (Subarray α) :=
  ⟨Subarray.empty⟩

instance : Inhabited (Subarray α) :=
  ⟨{}⟩

def isEmpty (as : Subarray α) : Bool :=
  as.start == as.stop

def contains [BEq α] (as : Subarray α) (a : α) : Bool :=
  as.any (· == a)

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

/--
Merge arrays `xs` and `ys`, which must be sorted according to `compare`. The
result is sorted as well. If two (or more) elements are equal according to
`compare`, they are preserved.
-/
def mergeSortedPreservingDuplicates [ord : Ord α] (xs ys : Array α) :
    Array α :=
  let acc := Array.mkEmpty (xs.size + ys.size)
  go acc 0 0
  where
    go (acc : Array α) (i j : Nat) : Array α :=
      if hi : i ≥ xs.size then
        acc ++ ys[j:]
      else if hj : j ≥ ys.size then
        acc ++ xs[i:]
      else
        have hi : i < xs.size := Nat.lt_of_not_le hi
        have hj : j < ys.size := Nat.lt_of_not_le hj
        have hij : i + j < xs.size + ys.size := Nat.add_lt_add hi hj
        let x := xs.get ⟨i, hi⟩
        let y := ys.get ⟨j, hj⟩
        if compare x y |>.isLE then
          have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
            rw [show i + 1 + j = i + j + 1 by simp_arith]
            exact Nat.sub_succ_lt_self _ _ hij
          go (acc.push x) (i + 1) j
        else
          have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
            Nat.sub_succ_lt_self _ _ hij
          go (acc.push y) i (j + 1)
    termination_by _ => xs.size + ys.size - (i + j)

/--
Merge arrays `xs` and `ys`, which must be sorted according to `compare` and must
not contain duplicates. The result is sorted as well. Equal elements are merged
using `merge`. If `xs` and `ys` do not contain duplicates according to
`compare`, then neither does the result.
-/
def mergeSortedMergingDuplicates [ord : Ord α] (xs ys : Array α)
    (merge : α → α → α) : Array α :=
  let acc := Array.mkEmpty (xs.size + ys.size)
  go acc 0 0
  where
    go (acc : Array α) (i j : Nat) : Array α :=
      if hi : i ≥ xs.size then
        acc ++ ys[j:]
      else if hj : j ≥ ys.size then
        acc ++ xs[i:]
      else
        have hi : i < xs.size := Nat.lt_of_not_le hi
        have hj : j < ys.size := Nat.lt_of_not_le hj
        have hij : i + j < xs.size + ys.size := Nat.add_lt_add hi hj
        let x := xs.get ⟨i, hi⟩
        let y := ys.get ⟨j, hj⟩
        match compare x y with
        | Ordering.lt =>
          have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
            rw [show i + 1 + j = i + j + 1 by simp_arith]
            exact Nat.sub_succ_lt_self _ _ hij
          go (acc.push x) (i + 1) j
        | Ordering.gt =>
          have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
            Nat.sub_succ_lt_self _ _ hij
          go (acc.push y) i (j + 1)
        | Ordering.eq =>
          have : xs.size + ys.size - (i + 1 + (j + 1)) < xs.size + ys.size - (i + j) := by
            rw [show i + 1 + (j + 1) = i + j + 2 by simp_arith]
            apply Nat.sub_add_lt_sub _ (by simp_arith)
            rw [show i + j + 2 = (i + 1) + (j + 1) by simp_arith]
            exact Nat.add_le_add hi hj
          go (acc.push (merge x y)) (i + 1) (j + 1)
    termination_by _ => xs.size + ys.size - (i + j)

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

def mergeAdjacentDuplicates [eq : BEq α] (f : α → α → α) (xs : Array α) :
    Array α :=
  if h : 0 < xs.size then loop #[] 1 (xs.get ⟨0, h⟩) else xs
  where
    loop (acc : Array α) (i : Nat) (hd : α) :=
      if h : i < xs.size then
        let x := xs.get ⟨i, h⟩
        if x == hd then
          loop acc (i + 1) (f hd x)
        else
          loop (acc.push hd) (i + 1) x
      else
        acc.push hd
    termination_by _ i _ => xs.size - i

set_option linter.unusedVariables false in
def deduplicateSorted [eq : BEq α] (xs : Array α) : Array α :=
  xs.mergeAdjacentDuplicates (λ x _ => x)

set_option linter.unusedVariables false in
def deduplicate [Inhabited α] [ord : Ord α] (xs : Array α) : Array α :=
  deduplicateSorted $ xs.qsort λ x y => compare x y |>.isLT

def equalSet [BEq α] (xs ys : Array α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

set_option linter.unusedVariables false in
def qsortOrd [Inhabited α] [ord : Ord α] (xs : Array α) : Array α :=
  xs.qsort λ x y => compare x y |>.isLT

set_option linter.unusedVariables false in
@[inline]
protected def maxD [ord : Ord α] (d : α) (xs : Array α) (start := 0)
    (stop := xs.size) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) λ max x =>
    if compare x max |>.isLT then max else x

set_option linter.unusedVariables false in
@[inline]
protected def max? [ord : Ord α] (xs : Array α) (start := 0)
    (stop := xs.size) : Option α :=
  if h : start < xs.size then
    some $ xs.maxD (xs.get ⟨start, h⟩) start stop
  else
    none

set_option linter.unusedVariables false in
@[inline]
protected def max [ord : Ord α] [Inhabited α] (xs : Array α) (start := 0)
    (stop := xs.size) : α :=
  xs.maxD default start stop

set_option linter.unusedVariables false in
@[inline]
protected def minD [ord : Ord α] (d : α) (xs : Array α) (start := 0)
    (stop := xs.size) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) λ min x =>
    if compare x min |>.isGE then min else x

set_option linter.unusedVariables false in
@[inline]
protected def min? [ord : Ord α] (xs : Array α) (start := 0)
    (stop := xs.size) : Option α :=
  if h : start < xs.size then
    some $ xs.minD (xs.get ⟨start, h⟩) start stop
  else
    none

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

def isAppOf' : Expr → Name → Bool
  | mdata _ b, d => isAppOf' b d
  | const c _, d => c == d
  | app f _,   d => isAppOf' f d
  | _,         _ => false

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


namespace Lean.HashSet

protected def ofArray [BEq α] [Hashable α] (as : Array α) : HashSet α :=
  HashSet.empty.insertMany as

@[inline]
def merge [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  s.insertMany t

def any [BEq α] [Hashable α] (s : HashSet α) (f : α → Bool) : Bool :=
  s.fold (init := false) λ result a => result || f a

def all [BEq α] [Hashable α] (s : HashSet α) (f : α → Bool) : Bool :=
  s.fold (init := true) λ result a => result && f a

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq s t := s.all (t.contains ·) && t.all (s.contains ·)

end Lean.HashSet


namespace Std.HashMap

variable [BEq α] [Hashable α]

def insertWith (m : HashMap α β) (a : α) (b : Unit → β) (f : β → β) :
    HashMap α β :=
  let b :=
    match m.find? a with
    | none => b ()
    | some b' => f b'
  m.insert a b

def updateM [Monad m] (map : HashMap α β) (k : α) (f : β → m β) :
    m (HashMap α β) :=
  match map.find? k with
  | some v => return map.insert k (← f v)
  | none => return map

@[inline]
def update (m : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  Id.run $ m.updateM a f

def merge (m n : HashMap α β) (combine : α → β → β → β) : HashMap α β :=
  if m.size < n.size then loop m n else loop n m
  where
    @[inline]
    loop m n :=
      m.fold (init := n) λ m a b =>
        m.insertWith a (λ _ => b) (λ b' => combine a b b')

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

def insertWith (m : PersistentHashMap α β) (k : α) (v : β) (f : β → β) :
    PersistentHashMap α β :=
  match m.find? k with
  | some v' => m.insert k (f v')
  | none => m.insert k v

def updateM [Monad m] (map : PersistentHashMap α β) (k : α) (f : β → m β) :
    m (PersistentHashMap α β) :=
  match map.find? k with
  | some v => return map.insert k (← f v)
  | none => return map

@[inline]
def update (m : PersistentHashMap α β) (k : α) (f : β → β) :
    PersistentHashMap α β :=
  Id.run $ m.updateM k f

def merge (m n : PersistentHashMap α β) (f : α → β → β → β) :
    PersistentHashMap α β :=
  if m.size < n.size then loop m n f else loop n m (λ a b b' => f a b' b)
  where
    @[inline]
    loop m n f := m.foldl (init := n) λ map k v =>
      map.insertWith k v λ v' => f k v v'

universe u v

def toArray (map : PersistentHashMap α β) : Array (α × β) :=
  map.foldl (init := Array.mkEmpty map.size) λ acc a b => acc.push (a, b)

end Lean.PersistentHashMap


namespace Lean.RBMap

@[inline]
def insertWith {cmp} (a : α) (b : β) (f : β → β) (m : RBMap α β cmp) :
    RBMap α β cmp :=
  match m.find? a with
  | none => m.insert a b
  | some b' => m.insert a (f b')

end Lean.RBMap


namespace Prod.Lex

instance [αeq_dec : DecidableEq α] {r : α → α → Prop} [r_dec : DecidableRel r]
    {s : β → β → Prop} [s_dec : DecidableRel s] : DecidableRel (Prod.Lex r s)
  | (a, b), (a', b') => by
    cases r_dec a a' with
    | isTrue raa' => exact isTrue $ left b b' raa'
    | isFalse nraa' =>
      cases αeq_dec a a' with
      | isTrue eq =>
        subst eq
        cases s_dec b b' with
        | isTrue sbb' => exact isTrue $ right a sbb'
        | isFalse nsbb' =>
          apply isFalse; intro contra; cases contra <;> contradiction
      | isFalse neqaa' =>
        apply isFalse; intro contra; cases contra <;> contradiction

end Prod.Lex


namespace Lean.Meta.DiscrTree

namespace Key

-- TODO could be more efficient.
protected def cmp (k l : Key s) : Ordering :=
  if lt k l then
    Ordering.lt
  else if lt l k then
    Ordering.gt
  else
    Ordering.eq

instance : Ord (Key s) :=
  ⟨Key.cmp⟩

end Key

namespace Trie

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
unsafe def foldMUnsafe [Monad m] (initialKeys : Array (Key s))
    (f : σ → Array (Key s) → α → m σ) (init : σ) : Trie α s → m σ
  | Trie.node vs children => do
    let s ← vs.foldlM (init := init) λ s v => f s initialKeys v
    children.foldlM (init := s) λ s (k, t) =>
      t.foldMUnsafe (initialKeys.push k) f s

@[implemented_by foldMUnsafe]
opaque foldM [Monad m] (initalKeys : Array (Key s))
    (f : σ → Array (Key s) → α → m σ) (init : σ) (t : Trie α s) : m σ :=
  pure init

@[inline]
def fold (initialKeys : Array (Key s)) (f : σ → Array (Key s) → α → σ)
    (init : σ) (t : Trie α s) : σ :=
  Id.run $ t.foldM initialKeys (init := init) λ s k a => return f s k a

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
unsafe def foldValuesMUnsafe [Monad m] (f : σ → α → m σ) (init : σ) :
    Trie α s → m σ
| node vs children => do
  let s ← vs.foldlM (init := init) f
  children.foldlM (init := s) λ s (_, c) => c.foldValuesMUnsafe (init := s) f

@[implemented_by foldValuesMUnsafe]
opaque foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : Trie α s) :
    m σ :=
  pure init

@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α s) : σ :=
  Id.run $ t.foldValuesM (init := init) f

partial def size : Trie α s → Nat
  | Trie.node vs children =>
    children.foldl (init := vs.size) λ n (_, c) => n + size c

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
def foldM [Monad m] (f : σ → Array (Key s) → α → m σ) (init : σ)
    (t : DiscrTree α s) : m σ :=
  t.root.foldlM (init := init) λ s k t => t.foldM #[k] (init := s) f

@[inline]
def fold (f : σ → Array (Key s) → α → σ) (init : σ) (t : DiscrTree α s) : σ :=
  Id.run $ t.foldM (init := init) λ s keys a => return f s keys a

@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α s) :
    m σ :=
  t.root.foldlM (init := init) λ s _ t => t.foldValuesM (init := s) f

@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α s) : σ :=
  Id.run $ t.foldValuesM (init := init) f

def values (t : DiscrTree α s) : Array α :=
  t.foldValues (init := #[]) λ as a => as.push a

def toArray (t : DiscrTree α s) : Array (Array (Key s) × α) :=
  t.fold (init := #[]) λ as keys a => as.push (keys, a)

def size (t : DiscrTree α s) : Nat :=
  t.root.foldl (init := 0) λ n _ t => n + t.size

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

def unhygienic [Monad m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions (·.setBool `tactic.hygienic false) x

-- Runs `tac` on `goal`, then on the subgoals created by `tac`, etc. Returns the
-- goals to which `tac` does not apply any more. If `tac` applies infinitely
-- often, `saturate1` diverges. If `tac` does not apply to `goal`, `none` is
-- returned.
partial def saturate1 (goal : MVarId)
    (tac : MVarId → MetaM (Option (Array MVarId))) :
    MetaM (Option (Array MVarId)) := do
  match ← tac goal with
  | none => return none
  | some goals => return some (← goals.forM go |>.run #[]).snd
  where
    go (goal : MVarId) : StateRefT (Array MVarId) MetaM Unit :=
      withIncRecDepth do
        match ← tac goal with
        | none => modify λ s => s.push goal
        | some goals => goals.forM go

partial def _root_.Lean.MVarId.getMVarDependencies (mvarId : MVarId)
    (includeDelayed := false) : MetaM (HashSet MVarId) :=
  return (← go mvarId |>.run {}).snd
  where
    addMVars (e : Expr) : StateRefT (HashSet MVarId) MetaM Unit := do
      let mvars ← getMVars e
      let mut s ← get
      set ({} : HashSet MVarId) -- Ensure that `s` is not shared.
      for mvarId in mvars do
        if ← pure includeDelayed <||> notM (mvarId.isDelayedAssigned) then
          s := s.insert mvarId
      set s
      mvars.forM go

    go (mvarId : MVarId) : StateRefT (HashSet MVarId) MetaM Unit :=
      withIncRecDepth do
        mvarId.instantiateMVars
        let mdecl ← mvarId.getDecl
        addMVars mdecl.type
        for ldecl in mdecl.lctx do
          addMVars ldecl.type
          if let (some val) := ldecl.value? then
            addMVars val
        if let (some ass) ← getDelayedMVarAssignment? mvarId then
          let pendingMVarId := ass.mvarIdPending
          if ← notM pendingMVarId.isAssignedOrDelayedAssigned then
            modify (·.insert pendingMVarId)
          go pendingMVarId

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


namespace Lean.Meta

def mkFreshIdWithPrefix [Monad m] [MonadNameGenerator m] («prefix» : Name) :
    m Name := do
  let ngen ← getNGen
  let r := { ngen with namePrefix := «prefix» }.curr
  setNGen ngen.next
  pure r

end Lean.Meta
