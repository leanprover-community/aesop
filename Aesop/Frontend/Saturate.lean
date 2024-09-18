/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Saturate
import Aesop.Frontend.Extension
import Aesop.Builder.Forward

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.PrettyPrinter

namespace Aesop.Frontend.Parser

syntax usingRuleSets := "using " ident+
syntax additionalRule := "*" <|> term
syntax additionalRules := "[" additionalRule,* "]"

end Parser

open Parser

def _root_.Aesop.ElabM.runForwardElab (goal : MVarId) (x : ElabM α) :
    TermElabM α :=
  x |>.run { parsePriorities := true, goal }

def mkForwardOptions (maxDepth? : Option Nat) (traceScript : Bool) :
    CoreM Options' :=
  ({ traceScript } : Aesop.Options).toOptions' maxDepth?

def elabGlobalRuleSets (rsNames : Array Ident) :
    CoreM (Array (GlobalRuleSet × Name × Name)) := do
  getGlobalRuleSets $
    (← getDefaultRuleSetNames).toArray ++ rsNames.map (·.getId)

def elabForwardRule (term : Term) : ElabM LocalRuleSetMember := do
  let builderInput := {
    options := ∅
    phase := .safe { penalty := 1, safety := .safe }
    term
  }
  let ctx := { parsePriorities := true, goal := (← read).goal }
  RuleBuilder.forward (isDestruct := false) builderInput |>.run ctx

def mkHypForwardRule (fvarId : FVarId) : ElabM LocalRuleSetMember := do
  elabForwardRule (← delab $ .fvar fvarId)

-- TODO mv
def isImplication (e : Expr) : MetaM Bool :=
  forallBoundedTelescope e (some 1) λ args body =>
    pure (! args.isEmpty) <&&> isProp body

def mkHypImplicationRule? (fvarId : FVarId) :
    ElabM (Option LocalRuleSetMember) := do
  let goal := (← read).goal
  goal.withContext do
  withTransparency .reducible do
    if ← isImplication (← fvarId.getType) then
        mkHypForwardRule fvarId
    else
        return none

def addLocalImplications (rs : LocalRuleSet) : ElabM LocalRuleSet := do
  let goal := (← read).goal
  let mut rs := rs
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then
      continue
    if let some rsMember ← mkHypImplicationRule? ldecl.fvarId then
      rs := rs.add rsMember
  return rs

def elabAdditionalForwardRules (rs : LocalRuleSet) (rules : Array (TSyntax ``additionalRule)) : ElabM LocalRuleSet := do
  let mut rs := rs
  let mut addImplications := false
  for rule in rules do
    match rule with
    | `(additionalRule| *) => addImplications := true
    | `(additionalRule| $t:term) => do
      rs := rs.add (← elabForwardRule t)
    | _ => throwUnsupportedSyntax
  if addImplications then
    rs ← addLocalImplications rs
  return rs

def elabForwardRuleSetCore (rsNames : Array Ident)
    (additionalRules : Array (TSyntax ``additionalRule))
    (options : Options') : ElabM LocalRuleSet := do
  let rss ← elabGlobalRuleSets rsNames
  let rs ← mkLocalRuleSet rss options
  elabAdditionalForwardRules rs additionalRules

def elabForwardRuleSet (rsNames? : Option (TSyntax ``usingRuleSets))
    (additionalRules? : Option (TSyntax ``additionalRules)) (options : Options') :
    ElabM LocalRuleSet := do
  let rsNames? ← rsNames?.mapM λ
    | `(usingRuleSets| using $rs:ident*) => pure rs
    | _ => throwUnsupportedSyntax
  let additionalRules? ← additionalRules?.mapM λ
    | `(additionalRules| [$rs:additionalRule,*]) => pure (rs : Array _)
    | _ => throwUnsupportedSyntax
  elabForwardRuleSetCore (rsNames?.getD #[]) (additionalRules?.getD #[]) options

open Lean.Elab.Tactic

def evalSaturate (depth? : Option (TSyntax `num))
    (rules? : Option (TSyntax ``additionalRules))
    (rs? : Option (TSyntax ``usingRuleSets)) (traceScript : Bool) :
    TacticM Unit := do
  let depth? := depth?.map (·.getNat)
  let options ← mkForwardOptions depth? traceScript
  let rs ← elabForwardRuleSet rs? rules? options
    |>.runForwardElab (← getMainGoal)
  liftMetaTactic1 (saturate rs · options)

elab "saturate " depth?:(num)? ppSpace rules?:(additionalRules)? ppSpace rs?:(usingRuleSets)? : tactic => do
  evalSaturate depth? rules? rs? (traceScript := false)

elab "saturate? " depth?:(num)? ppSpace rules?:(additionalRules)? ppSpace rs?:(usingRuleSets)? : tactic => do
  evalSaturate depth? rules? rs? (traceScript := true)

macro "forward " rules?:(additionalRules)? ppSpace rs?:(usingRuleSets)? : tactic =>
  `(tactic| saturate 1 $[$rules?]? $[$rs?]?)

macro "forward? " rules?:(additionalRules)? ppSpace rs?:(usingRuleSets)? : tactic =>
  `(tactic| saturate? 1 $[$rules?]? $[$rs?]?)

end Aesop.Frontend
