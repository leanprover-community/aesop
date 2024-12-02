/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.ElabM

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Tactic

namespace Aesop

def elabGlobalRuleIdent? (stx : Term) : TermElabM (Option Name) :=
  try
    if ! stx.raw.isIdent then
      return none
    let some (.const n _) ← resolveId? stx
      | return none
    return some n
  catch _ =>
    return none

def elabInductiveRuleIdent? (stx : Term) : TermElabM (Option InductiveVal) := do
  let some decl ← elabGlobalRuleIdent? stx
    | return none
  try
    getConstInfoInduct decl
  catch _ =>
    return none

-- HACK: We ignore the output goals, so this is only likely to work for
-- functions that might as well be in `TermElabM`.
def runTacticMAsTermElabM (goal : MVarId) (x : TacticM α) : TermElabM α := do
  x.run { elaborator := .anonymous } |>.run' { goals := [goal] }

-- HACK: We ignore the output goals, so this is only likely to work for
-- functions that might as well be in `TermElabM`.
def runTacticMAsElabM (x : TacticM α) : ElabM α := do
  runTacticMAsTermElabM (← read).goal x

def withFullElaboration (x : TermElabM α) : TermElabM α :=
  withSynthesize $ withoutErrToSorry $ withoutAutoBoundImplicit x

def elabRuleTermForApplyLikeCore (goal : MVarId) (stx : Term): TermElabM Expr :=
  withFullElaboration $ runTacticMAsTermElabM goal do
    elabTermForApply stx (mayPostpone := false)

def elabRuleTermForApplyLikeMetaM (goal : MVarId) (stx : Term) : MetaM Expr :=
  elabRuleTermForApplyLikeCore goal stx |>.run'

def elabRuleTermForApplyLike (stx : Term) : ElabM Expr := do
  elabRuleTermForApplyLikeCore (← read).goal stx

-- `stx` is of the form `"[" simpTheorem,* "]"`
def elabSimpTheorems (stx : Syntax) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
    TacticM (Simp.Context × Simp.SimprocsArray) :=
  withoutRecover do
    let kind : SimpKind := if isSimpAll then .simpAll else .simp
    let result ←
      elabSimpArgs stx ctx simprocs (eraseLocal := true) (kind := kind)
    if result.starArg then
      throwError "aesop: simp builder currently does not support wildcard '*'"
    return (result.ctx, result.simprocs)

-- HACK: This produces the syntax "[" lemmas,* "]" which is parsed by
-- `elabSimpArgs`. This syntax doesn't have an associated parser, so I don't
-- know how to ensure that the produced syntax is valid.
def mkSimpArgs (simpTheorem : Term) : Syntax :=
  mkNullNode #[
    mkAtom "[",
    mkNullNode
      #[Unhygienic.run `(Lean.Parser.Tactic.simpLemma| $simpTheorem:term)],
    mkAtom "]"
  ]

def elabRuleTermForSimpCore (goal : MVarId) (term : Term) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
    TermElabM (Simp.Context × Simp.SimprocsArray) := do
  withFullElaboration $ runTacticMAsTermElabM goal do
    elabSimpTheorems (mkSimpArgs term) ctx simprocs isSimpAll

def checkElabRuleTermForSimp (term : Term) (isSimpAll : Bool) : ElabM Unit := do
  let ctx ← Simp.mkContext (simpTheorems := #[{}] )
  let simprocs := #[{}]
  discard $ elabRuleTermForSimpCore (← read).goal term ctx simprocs isSimpAll

def elabRuleTermForSimpMetaM (goal : MVarId) (term : Term) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
    MetaM (Simp.Context × Simp.SimprocsArray) :=
  elabRuleTermForSimpCore goal term ctx simprocs isSimpAll |>.run'

end Aesop
