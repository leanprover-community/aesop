/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule.Name
import Aesop.Tracing

open Lean Lean.Meta

namespace Aesop

/--
A rule pattern. For a rule of type `∀ (x₀ : T₀) ... (xₙ : Tₙ), U`, a valid rule
pattern is an expression `p` such that `x₀ : T₁, ..., xₙ : Tₙ ⊢ p : P`. Let
`y₀, ..., yₖ` be those variables `xᵢ` on which `p` depends. When `p` matches an
expression `e`, this means that `e` is defeq to `p` (where each `yᵢ` is replaced
with a metavariable) and we obtain a substitution

    {y₀ ↦ t₀ : T₀, y₁ ↦ t₁ : T₁[x₀ := t₀], ...}

Now suppose we want to match the above rule type against a type `V` (where `V`
is the target for an `apply`-like rule and a hypothesis type for a
`forward`-like rule). To that end, we take `U` and replace each `xᵢ` where
`xᵢ = yⱼ` with `tⱼ` and each `xᵢ` with `xᵢ ≠ yⱼ ∀ j` with a metavariable. The
resulting expression `U'` is then matched against `V`.
-/
structure RulePattern where
  /--
  An expression of the form `λ y₀ ... yₖ, p` representing the
  pattern.
  -/
  pattern : AbstractMVarsResult
  /--
  A partial map from the index set `{0, ..., n-1}` into `{0, ..., k-1}`. If
  `argMap[i] = j`, this indicates that when matching against the rule type, the
  instantiation `tⱼ` of `yⱼ` should be substituted for `xᵢ`.
  -/
  argMap : Array (Option Nat)
  deriving Inhabited

namespace RulePattern

def «open» (pat : RulePattern) : MetaM (Array MVarId × Expr) := do
  let (mvarIds, _, p) ← openAbstractMVarsResult pat.pattern
  return (mvarIds.map (·.mvarId!), p)

end RulePattern

def RulePatternInstantiation := Array Expr
  deriving Inhabited, BEq, Hashable

def RulePatternInstantiation.toArray : RulePatternInstantiation → Array Expr :=
  id

instance : EmptyCollection RulePatternInstantiation :=
  ⟨.empty⟩

section

variable {ω : Type} {m : Type → Type} [STWorld ω m] [MonadLiftT (ST ω) m]
    [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]

def forEachExprInGoalCore (mvarId : MVarId) (g : Expr → m Bool) :
    MonadCacheT Expr Unit m Unit :=
  mvarId.withContext do
    for ldecl in ← show MetaM _ from getLCtx do
      if ldecl.isImplementationDetail then
        continue
      ForEachExpr.visit g ldecl.toExpr
      ForEachExpr.visit g ldecl.type
      if let some value := ldecl.value? then
        ForEachExpr.visit g value
    ForEachExpr.visit g (← mvarId.getType)

@[inline, always_inline]
def forEachExprInGoal' (mvarId : MVarId) (g : Expr → m Bool) : m Unit :=
  forEachExprInGoalCore mvarId g |>.run

@[inline, always_inline]
def forEachExprInGoal (mvarId : MVarId) (g : Expr → m Unit) : m Unit :=
  forEachExprInGoal' mvarId λ e => do g e; return true

end

def matchRulePatternsCore (pats : Array (RuleName × RulePattern))
    (mvarId : MVarId) :
    StateRefT (Std.HashMap RuleName (Std.HashSet RulePatternInstantiation)) MetaM Unit :=
  withNewMCtxDepth do -- TODO use (allowLevelAssignments := true)?
    let openPats ← pats.mapM λ (name, pat) => return (name, ← pat.open)
    let initialState ← show MetaM _ from saveState
    forEachExprInGoal mvarId λ e => do
      if e.hasLooseBVars then
        -- We don't visit subexpressions with loose bvars. Instantiations
        -- derived from such subexpressions would not be valid in the goal's
        -- context. E.g. if a rule `(x : T) → P x` has pattern `x` and we
        -- have the expression `λ (y : T), y` in the goal, then it makes no
        -- sense to match `y` and generate `P y`.
        return
      for (name, mvarIds, p) in openPats do
        initialState.restore
        -- The many `isDefEq` checks here are quite expensive. Perhaps a better
        -- strategy would be to reducibly normalise the goal once and for all.
        -- Then we could use a variant of `isDefEq` that only checks for
        -- syntactic equality up to mvars.
        if ← isDefEq e p then
          let instances ← mvarIds.mapM λ mvarId => do
            let mvar := .mvar mvarId
            let result ← instantiateMVars mvar
            if result == mvar then
              initialState.restore
              throwError "matchRulePatterns: while matching pattern '{p}' against expression '{e}': expected metavariable ?{(← mvarId.getDecl).userName} ({mvarId.name}) to be assigned"
            pure result
          modify λ m =>
            -- TODO loss of linearity?
            if let some instanceSet := m[name]? then
              m.insert name (instanceSet.insert instances)
            else
              m.insert name (.empty |>.insert instances)

def matchRulePatterns (pats : Array (RuleName × RulePattern))
    (mvarId : MVarId) :
    MetaM (Std.HashMap RuleName (Std.HashSet RulePatternInstantiation)) :=
  (·.snd) <$> (matchRulePatternsCore pats mvarId |>.run ∅)

namespace RulePattern

def getInstantiation [Monad m] [MonadError m] (pat : RulePattern)
    (inst : RulePatternInstantiation) (argIndex : Nat) : m (Option Expr) := do
  -- It's possible that `argMap[argIndex]? = none` if the rule type is
  -- syntactically `∀ (x₁ : T₁) ... (xₙ : Tₙ) = U` and `U` is a `forall` up to
  -- the rule's transparency.
  let some (some instIndex) := pat.argMap[argIndex]?
    | return none
  let some inst := inst.toArray[instIndex]?
    | throwError "getInstantiation: expected {instIndex} to be a valid instantiation index, but RulePatternInstantiation has size {inst.toArray.size}"
  return some inst

def openRuleType (pat : RulePattern) (inst : RulePatternInstantiation)
    (type : Expr) :
    MetaM (Array Expr × Array BinderInfo × Expr × Std.HashSet MVarId) := do
  let (mvars, binfos, body) ← forallMetaTelescopeReducing type
  let mut assigned := ∅
  for h : i in [:mvars.size] do
    if let some inst ← pat.getInstantiation inst i then
      let mvarId := mvars[i]'h.2 |>.mvarId!
      -- We use `isDefEq` to make sure that universe metavariables occurring in
      -- the type of `mvarId` are assigned.
      if ← isDefEq (.mvar mvarId) inst then
        assigned := assigned.insert mvarId
      else
        throwError "openRuleType: type-incorrect pattern instantiation: argument has type '{← mvarId.getType}' but pattern instantiation '{inst}' has type '{← inferType inst}'"
  return (mvars, binfos, body, assigned)

def specializeRule (pat : RulePattern) (inst : RulePatternInstantiation)
    (rule : Expr) : MetaM Expr :=
  withNewMCtxDepth do
    forallTelescopeReducing (← inferType rule) λ fvarIds _ => do
      let mut args := Array.mkEmpty fvarIds.size
      let mut remainingFVarIds := Array.mkEmpty fvarIds.size
      for h : i in [:fvarIds.size] do
        if let some inst ← pat.getInstantiation inst i then
          args := args.push $ some inst
        else
          let fvarId := fvarIds[i]'h.2
          args := args.push $ some fvarId
          remainingFVarIds := remainingFVarIds.push fvarId
      let result ← mkLambdaFVars remainingFVarIds (← mkAppOptM' rule args)
      return result

open Lean.Elab Lean.Elab.Term

def «elab» (stx : Term) (ruleType : Expr) : TermElabM RulePattern :=
  withLCtx {} {} $ withoutModifyingState do
    forallTelescope ruleType λ fvars _ => do
      let pat := (← elabPattern stx).consumeMData
      let (pat, mvarIds) ← fvarsToMVars fvars pat
      let (pat, mvarIdToPatternPos) ← abstractMVars' pat
      let argMap := mvarIds.map (mvarIdToPatternPos[·]?)
      aesop_trace[debug] "pattern '{stx}' elaborated into '{pat.expr}'"
      return { pattern := pat, argMap }
where
  fvarsToMVars (fvars : Array Expr) (e : Expr) :
      MetaM (Expr × Array MVarId) := do
    let e ← mkLambdaFVars fvars (← instantiateMVars e)
    let (mvars, _, e) ← lambdaMetaTelescope e (maxMVars? := some fvars.size)
    return (e, mvars.map (·.mvarId!))

  setMVarUserNamesToUniqueNames (e : Expr) : MetaM Unit := do
    let mvarIds ← getMVarDependencies e
    for mvarId in mvarIds do
      mvarId.setUserName mvarId.name

  -- Largely copy-pasta of `abstractMVars`.
  abstractMVars' (e : Expr) :
      MetaM (AbstractMVarsResult × Std.HashMap MVarId Nat) := do
    let e ← instantiateMVars e
    setMVarUserNamesToUniqueNames e
    let (e, s) := AbstractMVars.abstractExprMVars e
      { mctx := (← getMCtx)
        lctx := (← getLCtx)
        ngen := (← getNGen)
        abstractLevels := true }
    setNGen s.ngen
    setMCtx s.mctx
    let e := s.lctx.mkLambda s.fvars e
    let mut mvarIdToPos := ∅
    for h : i in [:s.fvars.size] do
      let name := s.lctx.get! (s.fvars[i]'h.2).fvarId! |>.userName
      mvarIdToPos := mvarIdToPos.insert ⟨name⟩ i
    let result :=
      { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }
    return (result, mvarIdToPos)

end Aesop.RulePattern
