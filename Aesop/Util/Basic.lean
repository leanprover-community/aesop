/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Aesop.Nanos
import Aesop.Util.UnionFind
import Aesop.Util.UnorderedArraySet
import Std.Lean.Expr
import Std.Lean.Format
import Std.Lean.Meta.DiscrTree
import Std.Lean.PersistentHashSet
import Std.Tactic.TryThis

open Lean
open Lean.Meta

namespace Aesop.Subarray

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

@[inline]
def time [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Aesop.Nanos) := do
  let start ← IO.monoNanosNow
  let a ← x
  let stop ← IO.monoNanosNow
  return (a, ⟨stop - start⟩)

@[inline]
def time' [Monad m] [MonadLiftT BaseIO m] (x : m Unit) : m Aesop.Nanos := do
  let start ← IO.monoNanosNow
  x
  let stop ← IO.monoNanosNow
  return ⟨stop - start⟩

namespace HashSet

-- TODO reuse old hash set instead of building a new one.
def filter [BEq α] [Hashable α] (hs : HashSet α) (p : α → Bool) : HashSet α :=
  hs.fold (init := ∅) λ hs a => if p a then hs.insert a else hs

end HashSet

namespace PersistentHashSet

-- Elements are returned in unspecified order.
@[inline]
def toList [BEq α] [Hashable α] (s : PersistentHashSet α) :
    List α :=
  s.fold (init := []) λ as a => a :: as

-- Elements are returned in unspecified order. (In fact, they are currently
-- returned in reverse order of `toList`.)
@[inline]
def toArray [BEq α] [Hashable α] (s : PersistentHashSet α) :
    Array α :=
  s.fold (init := Array.mkEmpty s.size) λ as a => as.push a

end PersistentHashSet

section DiscrTree

open DiscrTree

-- For `type = ∀ (x₁, ..., xₙ), T`, returns keys that match `T * ... *` (with
-- `n` stars).
def getConclusionDiscrTreeKeys (type : Expr) (config : WhnfCoreConfig) :
    MetaM (Array Key) :=
  withoutModifyingState do
    let (_, _, conclusion) ← forallMetaTelescope type
    mkPath conclusion config
    -- We use a meta telescope because `DiscrTree.mkPath` ignores metas (they
    -- turn into `Key.star`) but not fvars.

-- For a constant `d` with type `∀ (x₁, ..., xₙ), T`, returns keys that
-- match `d * ... *` (with `n` stars).
def getConstDiscrTreeKeys (decl : Name) : MetaM (Array Key) := do
  let arity := (← getConstInfo decl).type.forallArity
  let mut keys := Array.mkEmpty (arity + 1)
  keys := keys.push $ .const decl arity
  for _ in [0:arity] do
    keys := keys.push $ .star
  return keys

def isEmptyTrie : Trie α → Bool
  | .node vs children => vs.isEmpty && children.isEmpty

@[specialize]
private partial def filterTrieM [Monad m] [Inhabited σ] (f : σ → α → m σ)
    (p : α → m (ULift Bool)) (init : σ) : Trie α → m (Trie α × σ)
  | .node vs children => do
    let (vs, acc) ← vs.foldlM (init := (#[], init)) λ (vs, acc) v => do
      if (← p v).down then
        return (vs.push v, acc)
      else
        return (vs, ← f acc v)
    let (children, acc) ← go acc 0 children
    let children := children.filter λ (_, c) => ! isEmptyTrie c
    return (.node vs children, acc)
  where
    go (acc : σ) (i : Nat) (children : Array (Key × Trie α)) :
        m (Array (Key × Trie α) × σ) := do
      if h : i < children.size then
        let (key, t) := children[i]'h
        let (t, acc) ← filterTrieM f p acc t
        go acc (i + 1) (children.set ⟨i, h⟩ (key, t))
      else
        return (children, acc)

/--
Remove elements for which `p` returns `false` from the given `DiscrTree`.
The removed elements are monadically folded over using `f` and `init`, so `f`
is called once for each removed element and the final state of type `σ` is
returned.
-/
@[specialize]
def filterDiscrTreeM [Monad m] [Inhabited σ] (p : α → m (ULift Bool))
    (f : σ → α → m σ) (init : σ) (t : DiscrTree α) :
    m (DiscrTree α × σ) := do
  let (root, acc) ←
    t.root.foldlM (init := (.empty, init)) λ (root, acc) key t => do
      let (t, acc) ← filterTrieM f p acc t
      let root := if isEmptyTrie t then root else root.insert key t
      return (root, acc)
  return (⟨root⟩, acc)

/--
Remove elements for which `p` returns `false` from the given `DiscrTree`.
The removed elements are folded over using `f` and `init`, so `f` is called
once for each removed element and the final state of type `σ` is returned.
-/
def filterDiscrTree [Inhabited σ] (p : α → Bool) (f : σ → α → σ) (init : σ)
    (t : DiscrTree α) : DiscrTree α × σ := Id.run $
  filterDiscrTreeM (λ a => pure ⟨p a⟩) (λ s a => pure (f s a)) init t

end DiscrTree

namespace SimpTheorems

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
  foldSimpEntries (thms := thms) (init := #[]) λ s thm => s.push thm

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

end SimpTheorems


@[inline]
def setThe (σ) {m} [MonadStateOf σ m] (s : σ) : m PUnit :=
  MonadStateOf.set s

@[inline]
def runMetaMAsCoreM (x : MetaM α) : CoreM α :=
  Prod.fst <$> x.run {} {}

@[inline]
def runTermElabMAsCoreM (x : Elab.TermElabM α) : CoreM α :=
  runMetaMAsCoreM x.run'

def updateSimpEntryPriority (priority : Nat) (e : SimpEntry) : SimpEntry :=
  match e with
  | .thm t => .thm { t with priority }
  | .toUnfoldThms .. | .toUnfold .. => e

def isAppOfUpToDefeq (f : Expr) (e : Expr) : MetaM Bool :=
  withoutModifyingState do
    let type ← inferType f
    let (mvars, _, _) ← forallMetaTelescope type
    let app := mkAppN f mvars
    if ← isDefEq app e then
      return true
    else
      return false

/--
Partition an array of `MVarId`s into 'goals' and 'proper mvars'. An `MVarId`
from the input array `ms` is classified as a proper mvar if any of the `ms`
depend on it, and as a goal otherwise. Additionally, for each goal, we report
the set of mvars that the goal depends on.
-/
def partitionGoalsAndMVars (goals : Array MVarId) :
    MetaM (Array (MVarId × UnorderedArraySet MVarId) × UnorderedArraySet MVarId) := do
  let mut goalsAndMVars := #[]
  let mut mvars : UnorderedArraySet MVarId := {}
  for g in goals do
    let gMVars ← .ofHashSet <$> g.getMVarDependencies
    mvars := mvars.merge gMVars
    goalsAndMVars := goalsAndMVars.push (g, gMVars)
  let goals :=
    if mvars.isEmpty then
      goalsAndMVars
    else
      goalsAndMVars.filter λ (g, _) => ! mvars.contains g
  return (goals, mvars)

section TransparencySyntax

variable [Monad m] [MonadQuotation m]

open Parser.Tactic

def withTransparencySeqSyntax (md : TransparencyMode)
    (k : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) :=
  match md with
  | .default => return k
  | .all => `(tacticSeq| with_unfolding_all $k)
  | .reducible => `(tacticSeq| with_reducible $k)
  | .instances => `(tacticSeq| with_reducible_and_instances $k)

def withAllTransparencySeqSyntax (md : TransparencyMode)
    (k : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) :=
  match md with
  | .all => `(tacticSeq| with_unfolding_all $k)
  | _ => return k

def withTransparencySyntax (md : TransparencyMode) (k : TSyntax `tactic) :
    m (TSyntax `tactic) :=
  match md with
  | .default   => return k
  | .all       => `(tactic| with_unfolding_all $k:tactic)
  | .reducible => `(tactic| with_reducible $k:tactic)
  | .instances => `(tactic| with_reducible_and_instances $k:tactic)

def withAllTransparencySyntax (md : TransparencyMode) (k : TSyntax `tactic) :
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

-- Largely copy-pasta from Std.Tactic.TryThis.addSuggestion
-- I don't really know what's going on here; this is all cargo-culted. It seems
-- to work when `aesop?` appears on its own line, as in
--
-- ```lean
-- by
--   aesop?
-- ```
--
-- It doesn't work when `aesop?` is preceded by other text on the same line, as
-- in
--
-- ```lean
-- have x := by aesop?
-- ```
--
-- Also, the `Try this:` suggestion in the infoview is not properly formatted.
def addTryThisTacticSeqSuggestion (ref : Syntax)
    (suggestion : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (origSpan? : Option Syntax := none) : MetaM Unit := do
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq suggestion
  let msgText := fmt.prettyExtra (indent := 0) (column := 0)
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let start := findLineStart map.source range.start
    let indent := (range.start - start).1
    let text := fmt.prettyExtra (indent := indent - 2) (column := indent)
    let suggestion := {
      suggestion := .string text
      messageData? := some msgText
    }
    Std.Tactic.TryThis.addSuggestion ref suggestion (origSpan? := origSpan?)
      (header := "Try this:\n  ")

/--
Runs a computation for at most the given number of heartbeats times 1000,
ignoring the global heartbeat limit. Note that heartbeats spent on the
computation still count towards the global heartbeat count.
-/
def withMaxHeartbeats [Monad m] [MonadLiftT BaseIO m]
    [MonadWithReaderOf Core.Context m] (n : Nat) (x : m α) : m α := do
  let numHeartbeats ← IO.getNumHeartbeats
  let f s := {
    s with
    initHeartbeats := numHeartbeats
    maxHeartbeats := n * 1000
  }
  withReader f x

end Aesop
