/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean
import Std

open Std (HashSet PHashSet)


def BEq.ofOrd (ord : Ord α) : BEq α where
  beq x y :=
    match compare x y with
    | Ordering.eq => true
    | _ => false

instance (priority := low) [ord : Ord α] : BEq α :=
  BEq.ofOrd ord


namespace Option

def forM [Monad m] (f : α → m Unit) : Option α → m Unit
  | none => pure ()
  | some a => f a

def mergeLeftBiased : Option α → Option α → Option α
  | some x, y => some x
  | none, y => y

def mergeRightBiased : Option α → Option α → Option α
  | x, some y => some y
  | x, none => x

end Option


inductive Tri {α} (lt eq gt : α → α → Prop) (x y : α)
| lt (h : lt x y)
| eq (h : eq x y)
| gt (h : gt x y)

abbrev Trichotomous {α} (lt eq gt : α → α → Prop) :=
  ∀ x y, Tri lt eq gt x y


namespace Nat

theorem trichotomous_lt_eq_gt : @Trichotomous Nat (· < ·) (· = ·) (· > ·)
| zero, zero => Tri.eq rfl
| zero, succ m => Tri.lt $ zero_lt_succ _
| succ n, zero => Tri.gt $ zero_lt_succ _
| succ n, succ m =>
  match trichotomous_lt_eq_gt n m with
  | Tri.lt p => Tri.lt $ succ_lt_succ p
  | Tri.eq p => Tri.eq $ congrArg succ p
  | Tri.gt p => Tri.gt $ succ_lt_succ p

theorem lt_of_not_ge {n m : Nat} (h : ¬ n ≥ m) : n < m :=
  match trichotomous_lt_eq_gt n m with
  | Tri.lt p => p
  | Tri.eq p => False.elim $ h $ Nat.le_of_eq p.symm
  | Tri.gt p => False.elim $ h $ Nat.le_of_lt p

theorem sub_add_le_sub (n m k : Nat) : n - (m + k) ≤ n - m :=
  match k with
  | zero => Nat.le_of_eq rfl
  | succ k => Nat.le_trans (pred_le _) (sub_add_le_sub _ _ _)

theorem ne_zero_of_zero_lt {n : Nat} (h : 0 < n) : n ≠ 0 := λ contra =>
  match n with
  | zero => Nat.lt_irrefl _ h
  | succ n => by cases contra

theorem zero_sub_eq_zero : ∀ n, 0 - n = 0
  | zero => rfl
  | succ n => show pred (0 - n) = 0 by rw [zero_sub_eq_zero n]; rfl

theorem pred_sub : ∀ n m, pred (n - m) = pred n - m
  | zero, zero => rfl
  | zero, succ m =>
    show pred (0 - succ m) = 0 - succ m by
    rw [zero_sub_eq_zero]; rfl
  | succ n, zero => rfl
  | succ n, succ m => by
    show pred (pred (succ n - m)) = pred (pred (succ n) - m)
    rw [pred_sub (succ n) m]

theorem lt_pred_of_succ_lt {n m : Nat} : succ n < m → n < pred m
  | le.refl => Nat.lt_succ_self _
  | @le.step _ x h₂ => Nat.lt_trans (Nat.lt_succ_self _) h₂

theorem zero_lt_sub {n m : Nat} (h : m < n) : 0 < n - m :=
  match m with
  | zero => h
  | succ m => by
    show 0 < pred (n - m)
    rw [pred_sub]
    exact zero_lt_sub $ lt_pred_of_succ_lt h

theorem sub_add_lt_sub {n m k : Nat} (h₁ : m + k ≤ n) (h₂ : k ≠ 0) :
    n - (m + k) < n - m :=
  match k with
  | zero => h₂ rfl |>.elim
  | succ k =>
    Nat.lt_of_lt_of_le
      (pred_lt $ ne_zero_of_zero_lt $ zero_lt_sub $ lt_of_succ_le h₁)
      (sub_add_le_sub _ _ _)

end Nat


namespace String

def joinSep (sep : String) (ss : Array String) : String :=
  let firstNonempty? := ss.findIdx? (! ·.isEmpty)
  match firstNonempty? with
  | none => ""
  | some firstNonempty =>
    ss.foldl (start := firstNonempty + 1) (init := ss[firstNonempty]) λ res s =>
      if s.isEmpty then res else res ++ sep ++ s

end String


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

@[inline]
def compareLexicographic (cmp₁ : α → α → Ordering) (cmp₂ : α → α → Ordering)
    (x y : α) : Ordering :=
  match cmp₁ x y with
  | Ordering.eq => cmp₂ x y
  | ord => ord

end Ordering


namespace Ord

def isLT (o : Ord α) (x y : α) : Bool :=
  o.compare x y |>.isLT

def isLE (o : Ord α) (x y : α) : Bool :=
  o.compare x y |>.isLE

def isEQ (o : Ord α) (x y : α) : Bool :=
  o.compare x y |>.isEQ

def isGT (o : Ord α) (x y : α) : Bool :=
  o.compare x y |>.isGT

def isGE (o : Ord α) (x y : α) : Bool :=
  o.compare x y |>.isGE

def lexicographic (o₁ : Ord α) (o₂ : Ord α) : Ord α :=
  ⟨Ordering.compareLexicographic o₁.compare o₂.compare⟩

end Ord


@[inline]
def compareBy [Ord β] (f : α → β) (x y : α) : Ordering :=
  compare (f x) (f y)


namespace Subarray

instance : Inhabited (Subarray α) where
  default := {
    as := #[]
    start := 0
    stop := 0
    h₁ := Nat.le_refl 0
    h₂ := Nat.le_refl 0
  }

def contains [BEq α] (as : Subarray α) (a : α) : Bool :=
  as.any (· == a)

end Subarray


namespace Array

-- Merge arrays `xs` and `ys`. If `xs` and `ys` are sorted according to the
-- comparison function `le`, the result is as well. Duplicate elements are
-- preserved.
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
        have hi : i < xs.size :=
          Nat.lt_of_not_ge hi
        have hj : j < ys.size :=
          Nat.lt_of_not_ge hj
        have hij : i + j < xs.size + ys.size :=
          Nat.add_lt_add hi hj
        let x := xs.get ⟨i, hi⟩
        let y := ys.get ⟨j, hj⟩
        if compare x y |>.isLE then
          have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
            rw [Nat.add_assoc i 1 j, Nat.add_comm 1 j, ← Nat.add_assoc]
            exact Nat.sub_succ_lt_self _ _ hij
          go (acc.push x) (i + 1) j
        else
          have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
            Nat.sub_succ_lt_self _ _ hij
          go (acc.push y) i (j + 1)
    termination_by _ => xs.size + ys.size - (i + j)

-- Merge arrays `xs` and `ys`. If `xs` and `ys` are sorted according to
-- `compare`, the result is as well. Equal elements (meaning `x ∈ xs` and `y ∈
-- ys` such that `compare x y = eq`) are merged using `merge`. If `xs` and `ys`
-- do not contain duplicates according to `compare`, then neither does the
-- result.
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
        have hi : i < xs.size :=
          Nat.lt_of_not_ge hi
        have hj : j < ys.size :=
          Nat.lt_of_not_ge hj
        have hij : i + j < xs.size + ys.size :=
          Nat.add_lt_add hi hj
        let x := xs.get ⟨i, hi⟩
        let y := ys.get ⟨j, hj⟩
        match compare x y with
        | Ordering.lt =>
          have : xs.size + ys.size - (i + 1 + j) < xs.size + ys.size - (i + j) := by
            rw [Nat.add_assoc i 1 j, Nat.add_comm 1 j, ← Nat.add_assoc]
            exact Nat.sub_succ_lt_self _ _ hij
          go (acc.push x) (i + 1) j
        | Ordering.gt =>
          have : xs.size + ys.size - (i + j + 1) < xs.size + ys.size - (i + j) :=
            Nat.sub_succ_lt_self _ _ hij
          go (acc.push y) i (j + 1)
        | Ordering.eq =>
          have : xs.size + ys.size - (i + 1 + (j + 1)) < xs.size + ys.size - (i + j) := by -- fun :)
            rw [Nat.add_assoc i 1 (j + 1), Nat.add_comm 1 (j + 1)]
            show size xs + size ys - (i + (j + 2)) < size xs + size ys - (i + j)
            rw [← Nat.add_assoc]
            apply Nat.sub_add_lt_sub _ (by intro contra; cases contra)
            show i + j + (1 + 1) ≤ xs.size + ys.size
            rw [Nat.add_assoc i j (1 + 1), ← Nat.add_assoc j 1 1,
                Nat.add_comm (j + 1) 1, ← Nat.add_assoc i 1 (j + 1)]
            apply Nat.add_le_add hi hj
          go (acc.push (merge x y)) (i + 1) (j + 1)
    termination_by _ => xs.size + ys.size - (i + j)

def mergeSortedFilteringDuplicates [ord : Ord α] (xs ys : Array α) :
    Array α :=
  mergeSortedMergingDuplicates xs ys λ x y => x

-- Merge `xs` and `ys`, which do not need to be sorted. Elements which occur in
-- both `xs` and `ys` are only added once. If `xs` and `ys` do not contain
-- duplicates, then neither does the result. O(n*m)!
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

def deduplicateSorted [eq : BEq α] (xs : Array α) : Array α :=
  xs.mergeAdjacentDuplicates (λ x y => x)

def deduplicate [Inhabited α] [ord : Ord α] (xs : Array α) : Array α :=
  deduplicateSorted $ xs.qsort λ x y => compare x y |>.isLT

end Array


namespace IO

-- Returns elapsed time in milliseconds.
def time [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Nat) := do
  let start ← monoMsNow
  let a ← x
  let stop ← monoMsNow
  return (a, stop - start)

end IO


namespace Std.Format

@[inlineIfReduce]
def isEmptyShallow : Format → Bool
  | nil => true
  | text "" => true
  | _ => false

@[inline]
def indentDSkipEmpty [ToFormat α] (f : α) : Format :=
  let f := format f
  if f.isEmptyShallow then nil else indentD f

@[inline]
def unlines [ToFormat α] (fs : List α) : Format :=
  Format.joinSep fs line

@[inline]
def indentDUnlines [ToFormat α] : List α → Format :=
  indentDSkipEmpty ∘ unlines

@[inline]
def indentDUnlinesSkipEmpty [ToFormat α] (fs : List α) : Format :=
  indentDSkipEmpty $ unlines (fs.map format |>.filter (¬ ·.isEmptyShallow))

def formatIf (b : Bool) (f : Thunk Format) : Format :=
  if b then f.get else nil

end Std.Format


namespace Lean.MessageData

@[inline]
def join (ms : Array MessageData) : MessageData :=
ms.foldl (· ++ ·) nil

@[inlineIfReduce]
def isEmptyShallow : MessageData → Bool
  | ofFormat f => f.isEmptyShallow
  | _ => false

@[inline]
def indentDSkipEmpty (m : MessageData) : MessageData :=
  if m.isEmptyShallow then nil else indentD m

def joinSepArray (ms : Array MessageData) (sep : MessageData) :
    MessageData := Id.run do
  let mut result := nil
  let last := ms.size - 1
  for i in [0:ms.size] do
    if i ≥ last then
      result := result ++ ms[i]
    else
      result := result ++ ms[i] ++ sep
  return result

@[inline]
def unlines (ms : Array MessageData) : MessageData :=
  joinSepArray ms Format.line

@[inline]
def indentDUnlines : Array MessageData → MessageData :=
  indentDSkipEmpty ∘ unlines

@[inline]
def indentDUnlinesSkipEmpty (fs : Array MessageData) : MessageData :=
  indentDSkipEmpty $ unlines $ fs.filter (¬ ·.isEmptyShallow)

def toMessageDataIf (b : Bool) (f : Thunk MessageData) : MessageData :=
  if b then f.get else nil

def nodeFiltering (fs : Array (Option MessageData)) : MessageData :=
  node $ fs.filterMap id

end Lean.MessageData


namespace Std.HashSet

def insertMany [ForIn Id ρ α] [BEq α] [Hashable α] (s : HashSet α) (as : ρ) :
    HashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

instance [BEq α] [Hashable α] : ForIn m (HashSet α) α where
  forIn map init step := do
    let mut s := init
    for bucket in map.val.buckets.val do
      for x in bucket do
        match ← step x s with
        | ForInStep.done s' =>
          s := s'
          break
        | ForInStep.yield s' =>
          s := s'
    return s

@[inline]
def merge [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  if s.size < t.size then t.insertMany s else s.insertMany t

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq s t := Id.run do
    for x in s do
      unless t.contains x do
        return false
    for x in t do
      unless s.contains x do
        return false
    return true

end Std.HashSet


namespace Std.HashMap

variable [BEq α] [Hashable α]

def insertWith (m : HashMap α β) (a : α) (b : β) (f : β → β) : HashMap α β :=
  let b :=
    match m.find? a with
    | none => b
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
      m.fold (init := n) λ m a b => m.insertWith a b (λ b' => combine a b b')

end Std.HashMap


namespace Std.PersistentHashSet

@[inline]
def merge [BEq α] [Hashable α] (s t : PersistentHashSet α) : PersistentHashSet α :=
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

end Std.PersistentHashSet


namespace Std.PersistentHashMap

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

mutual
  @[specialize]
  private unsafe def mapMEntryImpl [Monad m] {β γ : Type u} (f : β → m γ)
      {α : Type u} : Entry α β (Node α β) → m (Entry α γ (Node α γ))
    | Entry.entry key val => Entry.entry key <$> f val
    | Entry.ref node => Entry.ref <$> mapMNodeImpl f node
    | Entry.null => pure Entry.null

  @[specialize]
  private unsafe def mapMNodeImpl [Monad m] {β γ : Type u} (f : β → m γ)
      {α : Type u} : Node α β → m (Node α γ)
    | Node.entries es => Node.entries <$> es.mapM (mapMEntryImpl f)
    | Node.collision ks vs h =>
      return Node.collision ks (← vs.mapM f) lcProof
      -- The lcProof here is conceptually trivial (it says that `vs.mapM f` has
      -- the same length as `vs`), but it would require a bit of effort because
      -- there seem to be no lemmas about array length in the library yet.
end

@[implementedBy mapMEntryImpl]
constant mapMEntry [Monad m] {β γ : Type u} (f : β → m γ) {α : Type u} :
    Entry α β (Node α β) → m (Entry α γ (Node α γ))

@[implementedBy mapMNodeImpl]
constant mapMNode [Monad m] {β γ : Type u} (f : β → m γ) {α : Type u} :
    Node α β → m (Node α γ)

@[inline]
def Entry.mapM [Monad m] : (β → m γ) → ∀ {α}, Entry α β (Node α β) →
    m (Entry α γ (Node α γ)) :=
  mapMEntry

@[inline]
def Node.mapM [Monad m] : (β → m γ) → ∀ {α}, Node α β → m (Node α γ) :=
  mapMNode

@[inline]
def mapM [Monad m] (f : β → m γ) {α} [BEq α] [Hashable α]
    (map : PersistentHashMap α β) : m (PersistentHashMap α γ) :=
  return {
    root := (← mapMNode f map.root)
    size := map.size
  }

def map (f : β → γ) {α} [BEq α] [Hashable α] (map : PersistentHashMap α β) :
    PersistentHashMap α γ :=
  Id.run $ map.mapM f

universe u v

-- We need to give u and v explicitly here, otherwise the compiler gets
-- confused.
unsafe def forInImpl [BEq α] [Hashable α] {m : Type u → Type v} [Monad m]
    (map : PersistentHashMap α β) (init : σ) (f : α × β → σ → m (ForInStep σ)) :
    m σ := do
  match (← go map.root init) with
  | ForInStep.yield r => pure r
  | ForInStep.done r => pure r
  where
    go : Node α β → σ → m (ForInStep σ)
      | Node.collision keys vals heq, acc =>
        let rec go' (i : Nat) (acc : σ) : m (ForInStep σ) := do
          if h : i < keys.size then
            let k := keys.get ⟨i, h⟩
            let v := vals.get ⟨i, heq ▸ h⟩
            match (← f (k, v) acc) with
            | ForInStep.done result => return ForInStep.done result
            | ForInStep.yield acc => go' (i + 1) acc
          else
            return ForInStep.yield acc
        go' 0 acc
      | Node.entries entries, acc => do
        let mut acc := acc
        for entry in entries do
          match entry with
          | Entry.null => pure ⟨⟩
          | Entry.entry k v =>
            match (← f (k, v) acc) with
            | ForInStep.done result => return ForInStep.done result
            | ForInStep.yield acc' => acc := acc'
          | Entry.ref node =>
            match (← go node acc) with
            | ForInStep.done result => return ForInStep.done result
            | ForInStep.yield acc' => acc := acc'
        return ForInStep.yield acc

-- Inhabited inference is being stupid here, so we can't use `partial`.
@[implementedBy forInImpl]
constant forIn [BEq α] [Hashable α] {m : Type u → Type v} [Monad m]
    (map : PersistentHashMap α β) (init : σ) (f : α × β → σ → m (ForInStep σ)) :
    m σ :=
  pure init

instance [BEq α] [Hashable α] : ForIn m (PersistentHashMap α β) (α × β) where
  forIn map := map.forIn

def toArray (map : PersistentHashMap α β) : Array (α × β) :=
  map.foldl (init := Array.mkEmpty map.size) λ acc a b => acc.push (a, b)

end Std.PersistentHashMap


namespace Std.RBMap

-- TODO horribly inefficient
@[inline]
def insertWith {cmp} (a : α) (b : β) (f : β → β) (m : RBMap α β cmp) :
    RBMap α β cmp :=
  match m.find? a with
  | none => m.insert a b
  | some b' => m.insert a (f b')

@[inline]
def mergeWith {cmp} (m n : RBMap α β cmp) (f : α → β → β → β) : RBMap α β cmp :=
  n.fold (init := m) λ m a b => m.insertWith a b λ b' => f a b' b

def insertArrayWith {cmp} (xs : Array (α × β)) (f : α → β → β → β)
    (m : RBMap α β cmp) : RBMap α β cmp :=
  xs.foldl (init := m) λ m (a, b) => m.insertWith a b λ b' => f a b' b

def insertListWith {cmp} (xs : List (α × β)) (f : α → β → β → β)
    (m : RBMap α β cmp) : RBMap α β cmp :=
  xs.foldl (init := m) λ m (a, b) => m.insertWith a b λ b' => f a b' b

def toArray {cmp} (m : RBMap α β cmp) : Array (α × β) :=
  m.fold (init := #[]) λ xs a b => xs.push (a, b)

end Std.RBMap


namespace Prod.Lex

instance [αeq_dec : DecidableEq α] {r : α → α → Prop} [r_dec : DecidableRel r]
    {s : β → β → Prop} [s_dec : DecidableRel s] : DecidableRel (Lex r s)
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
def cmp (k l : Key) : Ordering :=
  if lt k l then
    Ordering.lt
  else if lt l k then
    Ordering.gt
  else
    Ordering.eq

instance : Ord Key where
  compare := cmp

end Key

namespace Trie

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
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
  Id.run $ t.foldM initialKeys (init := init) λ s k a => return f s k a

-- This is just a partial function, but Lean doesn't realise that its type is
-- inhabited.
unsafe def foldValuesMUnsafe [Monad m] (f : σ → α → m σ) (init : σ) :
    Trie α → m σ
| node vs children => do
  let s ← vs.foldlM (init := init) f
  children.foldlM (init := s) λ s (k, c) => c.foldValuesMUnsafe (init := s) f

@[implementedBy foldValuesMUnsafe]
constant foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : Trie α) :
    m σ :=
  pure init

@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run $ t.foldValuesM (init := init) f

partial def size : Trie α → Nat
  | Trie.node vs children =>
    children.foldl (init := vs.size) λ n (k, c) => n + size c

partial def merge : Trie α → Trie α → Trie α
  | node vs₁ cs₁, node vs₂ cs₂ =>
    node (mergeValues vs₁ vs₂) (mergeChildren cs₁ cs₂)
  where
    mergeValues (vs₁ vs₂ : Array α) : Array α :=
      if vs₁.size > vs₂.size then vs₁ ++ vs₂ else vs₂ ++ vs₁

    mergeChildren (cs₁ cs₂ : Array (Key × Trie α)) : Array (Key × Trie α) :=
      have : Ord (Key × Trie α) :=
        ⟨λ (k₁, _) (k₂, _) => compare k₁ k₂⟩
      Array.mergeSortedMergingDuplicates cs₁ cs₂
        (λ (k₁, t₁) (k₂, t₂) => (k₁, merge t₁ t₂))

end Trie

@[inline]
def foldM [Monad m] (f : σ → Array Key → α → m σ) (init : σ) (t : DiscrTree α) :
    m σ :=
  t.root.foldlM (init := init) λ s k t => t.foldM #[k] (init := s) f

@[inline]
def fold (f : σ → Array Key → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run $ t.foldM (init := init) λ s keys a => return f s keys a

@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α) : m σ :=
  t.root.foldlM (init := init) λ s _ t => t.foldValuesM (init := s) f

@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run $ t.foldValuesM (init := init) f

def values (t : DiscrTree α) : Array α :=
  t.foldValues (init := #[]) λ as a => as.push a

def toArray (t : DiscrTree α) : Array (Array Key × α) :=
  t.fold (init := #[]) λ as keys a => as.push (keys, a)

def size (t : DiscrTree α) : Nat :=
  t.root.foldl (init := 0) λ n k t => n + t.size

@[inline]
def merge [BEq α] (t u : DiscrTree α) : DiscrTree α :=
  { root := t.root.merge u.root λ k trie₁ trie₂ => trie₁.merge trie₂ }

end DiscrTree

namespace SimpTheorems

def addSimpEntry (s : SimpTheorems) : SimpEntry → SimpTheorems
  | SimpEntry.thm l =>
    let s := addSimpTheoremEntry s l
    match l.name? with
    | some l => { s with erased := s.erased.erase l }
    | none => s
  | SimpEntry.toUnfold d =>
    { s with toUnfold := s.toUnfold.insert d }
  | SimpEntry.toUnfoldThms n thms => s.registerDeclToUnfoldThms n thms

def eraseSimpEntry (s : SimpTheorems) : SimpEntry → SimpTheorems
  | SimpEntry.thm l =>
    match l.name? with
    | some l =>
      { s with erased := s.erased.insert l, lemmaNames := s.lemmaNames.erase l }
    | none => s
  | SimpEntry.toUnfold d =>
    { s with toUnfold := s.toUnfold.erase d }
  | SimpEntry.toUnfoldThms n thms =>
    { s with toUnfoldThms := s.toUnfoldThms.erase n }

def merge (s t : SimpTheorems) : SimpTheorems := {
    pre := s.pre.merge t.pre
    post := s.post.merge t.post
    lemmaNames := s.lemmaNames.merge t.lemmaNames
    toUnfold := s.toUnfold.merge t.toUnfold
    toUnfoldThms := s.toUnfoldThms.merge t.toUnfoldThms
      (λ decl thms₁ thms₂ => thms₁)
      -- We can ignore collisions here because `thms₁` and `thms₂` should be
      -- identical.
    erased := mkErased t s $ mkErased s t {}
  }
  where
    -- Adds the erased lemmas from `s` to `init`, excluding those lemmas which
    -- occur in `t`.
    mkErased (s t : SimpTheorems) (init : PHashSet Name) : PHashSet Name :=
      s.erased.fold (init := init) λ x decl =>
        -- I think the following check suffices to ensure that `decl` does not
        -- occur in `t`. If `decl` is an unfold theorem (in the sense of
        -- `toUnfoldThms`), then it occurs also in `t.lemmaNames`.
        if t.lemmaNames.contains decl || t.toUnfold.contains decl then
          x
        else
          x.insert decl

open MessageData in
protected def toMessageData (s : SimpTheorems) : MessageData :=
  node #[
    "pre lemmas:" ++ node (s.pre.values.map toMessageData),
    "post lemmas:" ++ node (s.post.values.map toMessageData),
    "definitions to unfold:" ++ node
      (s.toUnfold.toArray.qsort Name.lt |>.map toMessageData),
    "erased entries:" ++ node
      (s.erased.toArray.qsort Name.lt |>.map toMessageData)
  ]

end SimpTheorems

-- Runs `tac` on `goal`, then on the subgoals created by `tac`, etc. Returns the
-- goals to which `tac` does not apply any more. If `tac` applies infinitely
-- often, `saturate'` diverges. If `tac` does not apply to `goal`, a singleton
-- array containing `goal` is returned.
partial def saturate' (goal : MVarId)
    (tac : MVarId → MetaM (Option (Array MVarId))) :
    MetaM (Array MVarId) :=
  return (← go goal |>.run #[]).snd
  where
    go (goal : MVarId) : StateRefT (Array MVarId) MetaM Unit :=
      withIncRecDepth do
        match ← tac goal with
        | none => modify λ s => s.push goal
        | some mvarIds => mvarIds.forM go

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

-- TODO The following defs are copied from Lean.Meta.Tactic.Simp.SimpTheorems

private partial def isPerm : Expr → Expr → MetaM Bool
  | Expr.app f₁ a₁ _, Expr.app f₂ a₂ _ => isPerm f₁ f₂ <&&> isPerm a₁ a₂
  | Expr.mdata _ s _, t => isPerm s t
  | s, Expr.mdata _ t _ => isPerm s t
  | s@(Expr.mvar ..), t@(Expr.mvar ..) => isDefEq s t
  | Expr.forallE n₁ d₁ b₁ _, Expr.forallE n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.lam n₁ d₁ b₁ _, Expr.lam n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.letE n₁ t₁ v₁ b₁ _, Expr.letE n₂ t₂ v₂ b₂ _ =>
    isPerm t₁ t₂ <&&> isPerm v₁ v₂ <&&> withLetDecl n₁ t₁ v₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.proj _ i₁ b₁ _, Expr.proj _ i₂ b₂ _ => pure (i₁ == i₂) <&&> isPerm b₁ b₂
  | s, t => return s == t

private def checkBadRewrite (lhs rhs : Expr) : MetaM Unit := do
  let lhs ← DiscrTree.whnfDT lhs (root := true)
  if lhs == rhs && lhs.isFVar then
    throwError "invalid `simp` theorem, equation is equivalent to{indentExpr (← mkEq lhs rhs)}"

private partial def shouldPreprocess (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs result => do
    if let some (_, lhs, rhs) := result.eq? then
      checkBadRewrite lhs rhs
      return false
    else
      return true

private partial def preprocess (e type : Expr) (inv : Bool) (isGlobal : Bool) : MetaM (List (Expr × Expr)) :=
  go e type
where
  go (e type : Expr) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← go e type
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if let some (_, lhs, rhs) := type.eq? then
    if isGlobal then
      checkBadRewrite lhs rhs
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm e
      return [(e, type)]
    else
      return [(e, type)]
  else if let some (lhs, rhs) := type.iff? then
    if isGlobal then
      checkBadRewrite lhs rhs
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm (← mkPropExt e)
      return [(e, type)]
    else
      let type ← mkEq lhs rhs
      let e    ← mkPropExt e
      return [(e, type)]
  else if let some (_, lhs, rhs) := type.ne? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq (← mkEq lhs rhs) (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some p := type.not? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq p (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← go e₁ type₁) ++ (← go e₂ type₂)
  else
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'True'"
    let type ← mkEq type (mkConst ``True)
    let e    ← mkEqTrue e
    return [(e, type)]

private def checkTypeIsProp (type : Expr) : MetaM Unit :=
  unless (← isProp type) do
    throwError "invalid 'simp', proposition expected{indentExpr type}"

private def mkSimpTheoremCore (e : Expr) (levelParams : Array Name) (proof : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpTheorem := do
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let type ← whnfR type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none => throwError "unexpected kind of 'simp' theorem{indentExpr type}"
    return { keys := keys, perm := perm, post := post, levelParams := levelParams, proof := proof, name? := name?, priority := prio }

def mkSimpTheoremsFromConst (declName : Name) (post : Bool) (inv : Bool) (prio : Nat) : MetaM (Array SimpTheorem) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if inv || (← shouldPreprocess type) then
      let mut r := #[]
      for (val, type) in (← preprocess val type inv (isGlobal := true)) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        r := r.push <| (← mkSimpTheoremCore (mkConst auxName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst auxName) post prio declName)
      return r
    else
      return #[← mkSimpTheoremCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst declName) post prio declName]

def instantiateMVarsInMVarType (mvarId : MVarId) : MetaM Expr := do
  let type := (← getMVarDecl mvarId).type
  if type.hasMVar then
    let type ← instantiateMVars type
    setMVarType mvarId type
    return type
  else
    return type

def instantiateMVarsInLocalDeclType (mvarId : MVarId) (fvarId : FVarId) :
    MetaM Expr := do
  let mdecl ← getMVarDecl mvarId
  let (some ldecl) := mdecl.lctx.find? fvarId | throwError
    "unknown local constant {fvarId.name} (in local context of metavariable ?{mvarId.name})"
  let type ← instantiateMVars ldecl.type
  let mdecl :=
    { mdecl with
      lctx := mdecl.lctx.modifyLocalDecl fvarId λ ldecl => ldecl.setType type }
  modify λ s =>
    { s with mctx := { s.mctx with decls := s.mctx.decls.insert mvarId mdecl } }
  return type

def instantiateMVarsInGoal (mvarId : MVarId) : MetaM Unit := do
  let mctx := (← get).mctx
  discard $ getMVarDecl mvarId
    -- The line above throws an error if the `mvarId` is not declared. The line
    -- below panics.
  let mctx := mctx.instantiateMVarDeclMVars mvarId
  modify λ s => { s with mctx := mctx }

def setMVarLCtx (mvarId : MVarId) (lctx : LocalContext) : MetaM Unit := do
  let newDecl := { ← getMVarDecl mvarId with lctx := lctx }
  let mctx ← getMCtx
  setMCtx { mctx with decls := mctx.decls.insert mvarId newDecl }

def setFVarBinderInfos (mvarId : MVarId) (fvars : Array FVarId)
    (bi : BinderInfo) : MetaM Unit := do
  let decl ← getMVarDecl mvarId
  let mut lctx := (← getMVarDecl mvarId).lctx
  for fvar in fvars do
    lctx := lctx.setBinderInfo fvar bi
  let mctx ← getMCtx
  let newDecl := { decl with lctx := lctx }
  setMCtx { mctx with decls := mctx.decls.insert mvarId newDecl }

structure HypothesisWithBinderInfo where
  userName : Name
  type : Expr
  value : Expr
  binderInfo : BinderInfo

def assertHypothesesWithBinderInfos (mvarId : MVarId)
    (hs : Array HypothesisWithBinderInfo) : MetaM (Array FVarId × MVarId) := do
  if hs.isEmpty then
    return (#[], mvarId)
  else withMVarContext mvarId do
    checkNotAssigned mvarId `assertHypotheses
    let tag    ← getMVarTag mvarId
    let target ← getMVarType mvarId
    let targetNew := hs.foldr (init := target) fun h targetNew =>
      mkForall h.userName h.binderInfo h.type targetNew
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let val := hs.foldl (init := mvarNew) fun val h => mkApp val h.value
    assignExprMVar mvarId val
    introNP mvarNew.mvarId! hs.size

-- TODO unused?
def copyMVar (mvarId : MVarId) : MetaM MVarId := do
  let decl ← getMVarDecl mvarId
  let mv ← mkFreshExprMVarAt decl.lctx decl.localInstances decl.type decl.kind
    decl.userName decl.numScopeArgs
  return mv.mvarId!

def runMetaMInSavedState (s : Meta.SavedState) (x : MetaM α) :
    MetaM (α × Meta.SavedState) :=
  withoutModifyingState do
    restoreState s
    let result ← x
    let finalState ← saveState
    return (result, finalState)

def runMetaMObservingFinalState (x : MetaM α) : MetaM (α × Meta.SavedState) :=
  withoutModifyingState do
    let result ← x
    let finalState ← saveState
    return (result, finalState)

def isValidMVarAssignment (mvarId : MVarId) (e : Expr) : MetaM Bool :=
  withMVarContext mvarId do
    let (some _) ← observing? $ check e | return false
    let et ← inferType e
    let mt := (← getMVarDecl mvarId).type
    withTransparency TransparencyMode.all $ isDefEq et mt

def isDeclaredMVar (mvarId : MVarId) : MetaM Bool := do
  match (← getMCtx).findDecl? mvarId with
  | some _ => pure true
  | none => pure false

def getHypMVarsNoDelayed (goal : MVarId) : MetaM (HashSet MVarId) := do
  instantiateMVarsInGoal goal
  withMVarContext goal do
    let mut mvars := HashSet.empty
    for hyp in (← getLCtx) do
      mvars := mvars.insertMany (← getMVarsNoDelayed (mkFVar hyp.fvarId))
    return mvars

def getTargetMVarsNoDelayed (goal : MVarId) : MetaM (Array MVarId) := do
  getMVarsNoDelayed (← instantiateMVarsInMVarType goal)

def getGoalMVarsNoDelayed (goal : MVarId) : MetaM (HashSet MVarId) := do
  let hypMVars ← getHypMVarsNoDelayed goal
  return hypMVars.insertMany (← getTargetMVarsNoDelayed goal)

end Lean.Meta


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


namespace Lean

open Lean.Elab
open Lean.Elab.Tactic

def runTacticMAsMetaM (tac : TacticM Unit) (goal : MVarId) :
    MetaM (List MVarId) :=
  run goal tac |>.run'

def runMetaMAsImportM (x : MetaM α) : ImportM α := do
  let ctx : Core.Context := { options := (← read).opts }
  let state : Core.State := { env := (← read).env }
  let r ← x |>.run {} {} |>.run ctx state |>.toIO'
  match r with
  | Except.ok ((a, _), _) => pure a
  | Except.error e => throw $ IO.userError (← e.toMessageData.toString)

def runMetaMAsCoreM (x : MetaM α) : CoreM α :=
  Prod.fst <$> x.run {} {}

def runTermElabMAsMetaM (x : TermElabM α) : MetaM α :=
  x.run'

end Lean


namespace Lean.Elab.Tactic

open Lean.Elab.Term
open Lean.Meta

syntax (name := Parser.runTactic) &"run" term : tactic

private abbrev TacticMUnit := TacticM Unit

-- TODO copied from evalExpr
unsafe def evalTacticMUnitUnsafe (value : Expr) : TermElabM (TacticM Unit) :=
  withoutModifyingEnv do
    let name ← mkFreshUserName `_tmp
    let type ← inferType value
    unless (← isDefEq type (mkConst ``TacticMUnit)) do
      throwError "unexpected type at evalTacticMUnit:{indentExpr type}"
    let decl := Declaration.defnDecl {
       name := name, levelParams := [], type := type,
       value := value, hints := ReducibilityHints.opaque,
       safety := DefinitionSafety.unsafe
    }
    ensureNoUnassignedMVars decl
    addAndCompile decl
    evalConst (TacticM Unit) name

@[implementedBy evalTacticMUnitUnsafe]
constant evalTacticMUnit : Expr → TermElabM (TacticM Unit)

@[tactic Parser.runTactic]
def evalRunTactic : Tactic
  | `(tactic|run $t:term) => do
    let t ← elabTerm t (some (mkApp (mkConst ``TacticM) (mkConst ``Unit)))
    (← evalTacticMUnit t)
  | _ => unreachable!

end Lean.Elab.Tactic


namespace String

def dropPrefix (s : String) (pre : String) : Option Substring :=
  let s := s.toSubstring
  if s.take pre.length == pre.toSubstring then
    s.drop pre.length
  else
    none

end String


namespace Substring

def parseIndexSuffix (s : Substring) : Option Nat :=
  if s.isEmpty then
    none
  else if s.front == '_' then
    s.drop 1 |>.toNat?
  else
    none

end Substring


namespace Lean.LocalContext

private inductive MatchUpToIndexSuffix
| exactMatch
| noMatch
| suffixMatch (i : Nat)

private def matchUpToIndexSuffix (n : Name) (query : Name) :
    MatchUpToIndexSuffix :=
  match n, query with
  | Name.str p₁ s₁ _, Name.str p₂ s₂ _ =>
    match s₁.dropPrefix s₂ with
    | none => MatchUpToIndexSuffix.noMatch
    | some suffix =>
      if suffix.isEmpty then
        MatchUpToIndexSuffix.exactMatch
      else
        match suffix.parseIndexSuffix with
        | none => MatchUpToIndexSuffix.noMatch
        | some i => MatchUpToIndexSuffix.suffixMatch i
  | n, query =>
    if n == query then
      MatchUpToIndexSuffix.exactMatch
    else
      MatchUpToIndexSuffix.noMatch

private def getUnusedUserNameIndex (lctx : LocalContext) (suggestion : Name) :
    Option Nat := Id.run do
  let mut minSuffix := none
  for ldecl in lctx do
    match matchUpToIndexSuffix ldecl.userName.eraseMacroScopes suggestion with
    | MatchUpToIndexSuffix.exactMatch =>
      minSuffix := updateMinSuffix minSuffix 1
    | MatchUpToIndexSuffix.noMatch =>
      continue
    | MatchUpToIndexSuffix.suffixMatch i =>
      minSuffix := updateMinSuffix minSuffix (i + 1)
  minSuffix
  where
    @[inline]
    updateMinSuffix : Option Nat → Nat → Option Nat
      | none, j => some j
      | some i, j => some $ i.max j

private def applyUserNameIndex (i : Option Nat) (suggestion : Name) : Name :=
  match i with
  | none => suggestion
  | some i => suggestion.appendIndexAfter i

def getUnusedName' (lctx : LocalContext) (suggestion : Name) : Name :=
  let suggestion := suggestion.eraseMacroScopes
  applyUserNameIndex (lctx.getUnusedUserNameIndex suggestion) suggestion

partial def getUnusedUserNames (lctx : LocalContext) (n : Nat) (suggestion : Name) :
    Array Name :=
  if n == 0 then
    #[]
  else
    let suggestion := suggestion.eraseMacroScopes
    let acc := Array.mkEmpty n
    match lctx.getUnusedUserNameIndex suggestion with
    | none => loop (acc.push suggestion) (n - 1) 1
    | some i => loop acc n i
  where
    loop (acc : Array Name) (n i : Nat) : Array Name :=
      match n with
      | 0 => acc
      | n + 1 => loop (acc.push $ suggestion.appendIndexAfter i) n (i + 1)

end LocalContext

def getUnusedUserName [Monad m] [MonadLCtx m] (suggestion : Name) : m Name :=
  return (← getLCtx).getUnusedName' suggestion

def getUnusedUserNames [Monad m] [MonadLCtx m] (n : Nat) (suggestion : Name) :
    m (Array Name) :=
  return (← getLCtx).getUnusedUserNames n suggestion

end Lean
