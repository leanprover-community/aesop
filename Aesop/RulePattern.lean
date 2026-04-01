/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Forward.Substitution
public import Aesop.BaseM
public import Aesop.Rule.Name
public import Aesop.Tracing
public import Aesop.Index.DiscrTreeConfig

public section

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
  /--
  A partial map from the level metavariables occurring in the rule to the
  pattern's level params.
  -/
  levelArgMap : Array (Option Nat)
  /--
  Discrimination tree keys for `p`.
  -/
  discrTreeKeys : Array DiscrTree.Key
  deriving Inhabited

namespace RulePattern

def boundPremises (pat : RulePattern) : Array Nat := Id.run do
  let mut result := Array.mkEmpty pat.argMap.size
  for h : i in [:pat.argMap.size] do
    if pat.argMap[i].isSome then
      result := result.push i
  return result

-- Largely copy-paste from openAbstractMVarsResult
def «open» (pat : RulePattern) :
    MetaM (Array MVarId × Array LMVarId × Expr) := do
  let a := pat.pattern
  let us ← a.paramNames.mapM fun _ => mkFreshLevelMVar
  let e := a.expr.instantiateLevelParamsArray a.paramNames us
  let (mvars, _, e) ← lambdaMetaTelescope e (some a.numMVars)
  return (mvars.map (·.mvarId!), us.map (·.mvarId!) , e)

def «match» (e : Expr) (pat : RulePattern) : BaseM (Option Substitution) :=
  withNewMCtxDepth do
    let (mvarIds, lmvarIds, p) ← pat.open
    if ! (← isDefEq e p) then
      return none
    let mut subst := .empty pat.argMap.size pat.levelArgMap.size
    for h : i in [:pat.argMap.size] do
      if let some j := pat.argMap[i] then
        let mvarId := mvarIds[j]!
        let mvar := .mvar mvarId
        let inst ← instantiateMVars mvar
        if inst == mvar then
          throwError "RulePattern.match: while matching pattern '{p}' against expression '{e}': expected metavariable ?{(← mvarId.getDecl).userName} ({mvarId.name}) to be assigned"
        subst := subst.insert ⟨i⟩ inst
    for h : i in [:pat.levelArgMap.size] do
      if let some j := pat.levelArgMap[i] then
        let mvar := .mvar lmvarIds[j]!
        let inst ← instantiateLevelMVars mvar
        if inst != mvar then
          subst := subst.insertLevel ⟨i⟩ inst
    return some subst

open Lean.Elab Lean.Elab.Term in
def «elab» (stx : Term) (rule : Expr) : TermElabM RulePattern :=
  withConstAesopTraceNode .debug (return m!"elaborating rule pattern") do
   -- TODO withNewMCtxDepth produces an error, but I don't understand why
  withLCtx {} {} $ withoutModifyingState do
    aesop_trace[debug] "rule: {rule}"
    aesop_trace[debug] "pattern: {stx}"
    let lmvarIds := collectLevelMVars {} (← instantiateMVars rule) |>.result
    aesop_trace[debug] "level metavariables in rule: {lmvarIds.map Level.mvar}"
    let (numArgs, pat) ← forallTelescope (← inferType rule) λ fvars _ => do
      let pat := (← elabPattern stx).consumeMData
      pure (fvars.size, ← mkLambdaFVars fvars pat)
    -- Create metavariables outside of the telescope to avoid false dependence on local context, for `abstractMVars`
    let (mvars, _, pat) ← lambdaMetaTelescope pat (maxMVars? := numArgs)
    let discrTreeKeys ← mkDiscrTreePath pat
    let pat ← abstractMVars pat
    let argMap := mvars.map (pat.exprArgs.idxOf? ·)
    let levelArgMap := lmvarIds.map (pat.lmvars.idxOf? <| .mvar ·)
    aesop_trace[debug] "result: '{pat.expr}' with arg map{indentD $ toMessageData argMap}\nand level arg map{indentD $ toMessageData levelArgMap}"
    return { pattern := pat, argMap, levelArgMap, discrTreeKeys }

end Aesop.RulePattern
