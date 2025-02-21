/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Index.Basic
import Aesop.RuleTac.GoalDiff
import Batteries.Lean.Meta.DiscrTree

set_option linter.missingDocs true

open Lean Lean.Meta

namespace Aesop

/-- A map from rule names to rule pattern substitutions. When run on a goal,
the rule pattern index returns such a map. -/
abbrev RulePatternSubstMap := Std.HashMap RuleName (Std.HashSet Substitution)

namespace RulePatternSubstMap

/-- Insert an array of rule pattern substitutions into a rule pattern
substitution map. -/
def insertArray (xs : Array (RuleName × Substitution))
    (m : RulePatternSubstMap) : RulePatternSubstMap :=
  xs.foldl (init := m) λ m (r, inst) =>
    match m[r]? with
    | none => m.insert r $ (∅ : Std.HashSet _).insert inst
    | some insts => m.insert r $ insts.insert inst

/-- Build a rule pattern substitution map from an array of substitutions. -/
def ofArray (xs : Array (RuleName × Substitution)) : RulePatternSubstMap :=
  (∅ : RulePatternSubstMap).insertArray xs

/-- Convert a rule pattern substitution map to a flat array of substitutions. -/
def toFlatArray (m : RulePatternSubstMap) : Array (RuleName × Substitution) :=
  m.fold (init := #[]) λ acc r patInsts =>
    patInsts.fold (init := acc) λ acc patInst =>
      acc.push (r, patInst)

end RulePatternSubstMap


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
  /-- The index. -/
  tree : DiscrTree RulePatternIndex.Entry
  /-- `true` iff the index contains no patterns. -/
  isEmpty : Bool
  deriving Inhabited

namespace RulePatternIndex

instance : EmptyCollection RulePatternIndex :=
  ⟨⟨{}, true⟩⟩

/-- Add a rule pattern to the index. -/
def add (name : RuleName) (pattern : RulePattern) (idx : RulePatternIndex) :
    RulePatternIndex :=
  ⟨idx.tree.insertCore pattern.discrTreeKeys { name, pattern }, false⟩

/-- Merge two rule pattern indices. Patterns that appear in both indices appear
twice in the result. -/
def merge (idx₁ idx₂ : RulePatternIndex) : RulePatternIndex :=
  if idx₁.isEmpty then
    idx₂
  else if idx₂.isEmpty then
    idx₁
  else
    ⟨idx₁.tree.mergePreservingDuplicates idx₂.tree, false⟩

section Get

/-- Get rule pattern substitutions for the patterns that match `e`. -/
def getSingle (e : Expr) (idx : RulePatternIndex) :
    BaseM (Array (RuleName × Substitution)) := do
  if idx.isEmpty then
    return #[]
  let ms ← getUnify idx.tree e
  ms.filterMapM λ { name := r, pattern } => do
    let some subst ← pattern.match e
      | return none
    return (r, subst)

/-- Get all substitutions of the rule patterns that match a subexpression of
`e`. Subexpressions containing bound variables are not considered. The returned
array may contain duplicates. -/
def getCore (e : Expr) (idx : RulePatternIndex) :
    BaseM (Array (RuleName × Substitution)) := do
  if idx.isEmpty then
    return #[]
  let e ← instantiateMVars e
  checkCache (β := RulePatternCache.Entry) e λ _ => do
    let (_, ms) ← e.forEach getSubexpr |>.run #[]
    return ms
where
  getSubexpr (e : Expr) :
      StateRefT (Array (RuleName × Substitution)) BaseM Unit := do
    if e.hasLooseBVars then
      -- We don't visit subexpressions with loose bvars. Substitutions
      -- derived from such subexpressions would not be valid in the goal's
      -- context. E.g. if a rule `(x : T) → P x` has pattern `x` and we
      -- have the expression `λ (y : T), y` in the goal, then it makes no
      -- sense to match `y` and generate `P y`.
      return
    let ms ← idx.getSingle e
    modifyThe (Array _) (· ++ ms)

@[inherit_doc getCore]
def get (e : Expr) (idx : RulePatternIndex) : BaseM RulePatternSubstMap :=
  .ofArray <$> idx.getCore e

/-- Get all substitutions of the rule patterns that match a subexpression of
the given local declaration. Subexpressions containing bound variables are not
considered. -/
def getInLocalDeclCore (acc : RulePatternSubstMap) (ldecl : LocalDecl)
    (idx : RulePatternIndex) : BaseM RulePatternSubstMap := do
  if idx.isEmpty then
    return acc
  let mut result := acc
  result := result.insertArray $ ← idx.getCore ldecl.toExpr
  result := result.insertArray $ ← idx.getCore ldecl.type
  if let some val := ldecl.value? then
    result := result.insertArray $ ← idx.getCore val
  return result

@[inherit_doc getInLocalDeclCore]
def getInLocalDecl (ldecl : LocalDecl) (idx : RulePatternIndex) :
    BaseM RulePatternSubstMap :=
  idx.getInLocalDeclCore ∅ ldecl

/-- Get all substitutions of the rule patterns that match a subexpression of
a hypothesis or the target. Subexpressions containing bound variables are not
considered. -/
def getInGoal (goal : MVarId) (idx : RulePatternIndex) :
    BaseM RulePatternSubstMap :=
  goal.withContext do
    if idx.isEmpty then
      return ∅
    let mut result := ∅
    for ldecl in (← goal.getDecl).lctx do
      unless ldecl.isImplementationDetail do
        result ← idx.getInLocalDeclCore result ldecl
    result := result.insertArray $ ← idx.getCore (← goal.getType)
    return result

end Get

end Aesop.RulePatternIndex
