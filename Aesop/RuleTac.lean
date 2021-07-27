/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Elab

open Lean
open Lean.Elab.Tactic
open Lean.Meta

namespace Aesop

-- A `RuleTacDescr` is a 'recipe' for constructing the tactic used by a rule.
-- When we serialise the rule set to an olean file, we serialise `RuleTacDescr`s
-- because we can't (currently?) serialise the actual tactics.
inductive RuleTacDescr
  | applyConst (decl : Name)
  | tactic (decl : Name)
  deriving Inhabited, BEq

-- A `RuleTac` bundles a `RuleTacDescr` and the tactic that was computed from
-- the description. Local rules do not have descriptions since we never
-- serialise them.
structure RuleTac where
  tac : TacticM Unit
  descr : Option RuleTacDescr
  deriving Inhabited

namespace RuleTacBuilder

/- Convenience for evalTacticUnsafe. -/
private abbrev TacticType := TacticM Unit

def checkTacticM (decl : Name) : MetaM Unit := do
  let info ← getConstInfo decl
  unless (← isDefEq info.type (mkConst ``TacticType)) do
    throwError "aesop: {decl} was expected to have type\n  TacticM Unit\nbut has type\n  {info.type}"

unsafe def evalTacticConstUnsafe (decl : Name) : TacticM Unit := do
  checkTacticM decl
    -- TODO Maybe we can elide the above check. We already check the type
    -- when we register the tactic.
  let tac ← evalConst TacticType decl
  tac

@[implementedBy evalTacticConstUnsafe]
constant evalTacticConst : Name → TacticM Unit
-- I think the above use of `evalConst` is safe because we call it at a concrete
-- type, making sure that the constant actually has that type.

def tactic (decl : Name) : MetaM RuleTac := do
  checkTacticM decl
  return { tac := evalTacticConst decl, descr := RuleTacDescr.tactic decl }

def apply (decl : Name) : MetaM RuleTac :=
  return {
    tac := liftMetaTactic λ goal => do
      Lean.Meta.apply goal (← mkConstWithFreshMVarLevels decl)
      -- TODO Go via apply tactic syntax to ensure intuitive behaviour?
    descr := RuleTacDescr.applyConst decl
  }

def applyFVar (userName : Name) : MetaM RuleTac := do
  let _ ← getLocalDeclFromUserName userName
  return {
    tac := liftMetaTactic λ goal => do
      let decl ← getLocalDeclFromUserName userName
      Lean.Meta.apply goal (mkFVar decl.fvarId)
    descr := none
  }

end RuleTacBuilder

namespace RuleTacDescr

def toRuleTac : RuleTacDescr → MetaM RuleTac
  | applyConst decl => RuleTacBuilder.apply decl
  | tactic decl => RuleTacBuilder.tactic decl

end RuleTacDescr

end Aesop
