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
