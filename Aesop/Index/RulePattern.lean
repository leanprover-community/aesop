/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.RulePattern
import Aesop.RuleTac.GoalDiff
import Batteries.Lean.Meta.DiscrTree

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- A map from rule names to rule pattern instantiations. When run on a goal,
the rule pattern index returns such a map. -/
abbrev RulePatternInstMap :=
  Std.HashMap RuleName (Std.HashSet RulePatternInstantiation)

namespace RulePatternInstMap

instance : EmptyCollection RulePatternInstMap :=
  ⟨{}⟩

/-- Insert an array of rule pattern instantiations into a rule pattern
instantiation map. -/
def insertArray (xs : Array (RuleName × RulePatternInstantiation))
    (m : RulePatternInstMap) : RulePatternInstMap :=
  xs.foldl (init := m) λ m (r, inst) =>
    match m[r]? with
    | none => m.insert r $ (∅ : Std.HashSet _).insert inst
    | some insts => m.insert r $ insts.insert inst

/-- Build a rule instantiation map from an array of instantiations. -/
def ofArray (xs : Array (RuleName × RulePatternInstantiation)) :
    RulePatternInstMap :=
  (∅ : RulePatternInstMap).insertArray xs

/-- Convert a rule instantiation map to a flat array of instantiations. -/
def toFlatArray (m : RulePatternInstMap) :
    Array (RuleName × RulePatternInstantiation) := Id.run do
  let mut result := #[]
  for (r, patInsts) in m do
    for patInst in patInsts do
      result := result.push (r, patInst)
  return result

end RulePatternInstMap

set_option linter.missingDocs false in
/-- A cache for the rule pattern index. -/
structure RulePatternCache where
  map : Std.HashMap Expr (Array (RuleName × RulePatternInstantiation))
  deriving Inhabited

instance : EmptyCollection RulePatternCache :=
  ⟨⟨∅⟩⟩

/-- Type class for monads with access to a rule pattern cache. -/
abbrev MonadRulePatternCache m :=
  MonadCache Expr (Array (RuleName × RulePatternInstantiation)) m

instance [Monad m] [MonadLiftT (ST ω) m] [STWorld ω m]
    [MonadStateOf RulePatternCache m] :
    MonadHashMapCacheAdapter Expr (Array (RuleName × RulePatternInstantiation)) m where
  getCache := return (← getThe RulePatternCache).map
  modifyCache f := modifyThe RulePatternCache λ s => { s with map := f s.map }

-- TODO upstream
scoped instance [MonadCache α β m] : MonadCache α β (StateRefT' ω σ m) where
  findCached? a := MonadCache.findCached? (m := m) a
  cache a b := MonadCache.cache (m := m) a b

/-- An entry of the rule pattern index. -/
structure RulePatternIndex.Entry where
  /-- The name of the rule to which the pattern belongs. -/
  name : RuleName
  /-- The rule's pattern. We assume that there is at most one pattern per
  rule. -/
  pattern : RulePattern
  deriving Inhabited

instance : BEq RulePatternIndex.Entry where
  beq e₁ e₂ := e₁.name == e₂.name

set_option linter.missingDocs false in
/-- A rule pattern index. Maps expressions `e` to rule patterns that likely
unify with `e`. -/
structure RulePatternIndex where
  tree : DiscrTree RulePatternIndex.Entry
  deriving Inhabited

namespace RulePatternIndex

instance : EmptyCollection RulePatternIndex :=
  ⟨⟨{}⟩⟩

/-- Add a rule pattern to the index. -/
def add (name : RuleName) (pattern : RulePattern) (idx : RulePatternIndex) :
    RulePatternIndex :=
  ⟨idx.tree.insertCore pattern.discrTreeKeys { name, pattern }⟩

/-- Merge two rule pattern indices. Patterns that appear in both indices appear
twice in the result. -/
def merge (idx₁ idx₂ : RulePatternIndex) : RulePatternIndex :=
  ⟨idx₁.tree.mergePreservingDuplicates idx₂.tree⟩

section Get

variable [Monad m] [MonadRulePatternCache m] [MonadLiftT MetaM m]
  [MonadControlT MetaM m]

local instance : STWorld IO.RealWorld m where

local instance : MonadLiftT (ST IO.RealWorld) m where
  monadLift x := (x : MetaM _)

local instance : MonadMCtx m where
  getMCtx := (getMCtx : MetaM _)
  modifyMCtx f := (modifyMCtx f : MetaM _)

/-- Get rule pattern instantiations for the patterns that match `e`. -/
def getSingle  (e : Expr) (idx : RulePatternIndex) :
    MetaM (Array (RuleName × RulePatternInstantiation)) := do
  let ms ← getUnify idx.tree e
  ms.foldlM (init := #[]) λ acc { name := r, pattern } =>
    withNewMCtxDepth do
      let (mvarIds, p) ← pattern.open
      if ← isDefEq e p then
        let inst ← mvarIds.mapM λ mvarId => do
          let mvar := .mvar mvarId
          let result ← instantiateMVars mvar
          if result == mvar then
            throwError "matchRulePatterns: while matching pattern '{p}' against expression '{e}': expected metavariable ?{(← mvarId.getDecl).userName} ({mvarId.name}) to be assigned"
          pure result
        return acc.push (r, inst)
      else
        return acc

/-- Get all instantiations of the rule patterns that match a subexpression of
`e`. Subexpressions containing bound variables are not considered. The returned
array may contain duplicates. -/
def getCore (e : Expr) (idx : RulePatternIndex) :
    m (Array (RuleName × RulePatternInstantiation)) := do
  let e ← instantiateMVars e
  checkCache e λ _ => (·.snd) <$> (e.forEach getSubexpr |>.run #[])
where
  getSubexpr (e : Expr) :
      StateRefT (Array (RuleName × RulePatternInstantiation)) m Unit := do
    if e.hasLooseBVars then
      -- We don't visit subexpressions with loose bvars. Instantiations
      -- derived from such subexpressions would not be valid in the goal's
      -- context. E.g. if a rule `(x : T) → P x` has pattern `x` and we
      -- have the expression `λ (y : T), y` in the goal, then it makes no
      -- sense to match `y` and generate `P y`.
      return
    let ms ← idx.getSingle e
    modify (· ++ ms)

@[inherit_doc getCore]
def get (e : Expr) (idx : RulePatternIndex) : m RulePatternInstMap :=
  .ofArray <$> idx.getCore e

/-- Get all instantiations of the rule patterns that match a subexpression of
the given local declaration. Subexpressions containing bound variables are not
considered. -/
def getInLocalDeclCore (acc : RulePatternInstMap) (ldecl : LocalDecl)
    (idx : RulePatternIndex) : m RulePatternInstMap := do
  let mut result := acc
  result := result.insertArray $ ← idx.getCore ldecl.toExpr
  result := result.insertArray $ ← idx.getCore ldecl.type
  if let some val := ldecl.value? then
    result := result.insertArray $ ← idx.getCore val
  return result

@[inherit_doc getInLocalDeclCore]
def getInLocalDecl (ldecl : LocalDecl) (idx : RulePatternIndex) :
    m RulePatternInstMap :=
  idx.getInLocalDeclCore ∅ ldecl

/-- Get all instantiations of the rule patterns that match a subexpression of
a hypothesis or the target. Subexpressions containing bound variables are not
considered. -/
def getInGoal (goal : MVarId) (idx : RulePatternIndex) : m RulePatternInstMap :=
  goal.withContext do
    let mut result := ∅
    for ldecl in (← goal.getDecl).lctx do
      unless ldecl.isImplementationDetail do
        result ← idx.getInLocalDeclCore result ldecl
    result := result.insertArray $ ← idx.getCore (← goal.getType)
    return result

end Get

end Aesop.RulePatternIndex
