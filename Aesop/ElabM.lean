/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

open Lean Lean.Meta Lean.Elab

namespace Aesop.ElabM

structure Context where
  parsePriorities : Bool
  goal : MVarId

namespace Context

def forAdditionalRules (goal : MVarId) : Context where
  parsePriorities := true
  goal := goal

-- HACK: Some of the elaboration functions require that we pass in the current
-- goal. The goal is used exclusively to look up fvars in the lctx, so when
-- we operate outside a goal, we pass in a dummy mvar with empty lctx.
def forAdditionalGlobalRules : MetaM Context := do
  let mvarId := (← mkFreshExprMVarAt {} {} (.const ``True [])).mvarId!
  return .forAdditionalRules mvarId

def forErasing (goal : MVarId) : Context where
  parsePriorities := false
  goal := goal

-- HACK: See `forAdditionalGlobalRules`
def forGlobalErasing : MetaM Context := do
  let mvarId := (← mkFreshExprMVarAt {} {} (.const ``True [])).mvarId!
  return .forErasing mvarId

end ElabM.Context


abbrev ElabM := ReaderT ElabM.Context $ TermElabM

-- Generate specialized pure/bind implementations so we don't need to optimise
-- them on the fly at each use site.
instance : Monad ElabM :=
  { inferInstanceAs (Monad ElabM) with }

protected def ElabM.run (ctx : Context) (x : ElabM α) : TermElabM α := do
  ReaderT.run x ctx

def shouldParsePriorities : ElabM Bool :=
  return (← read).parsePriorities

def getGoal : ElabM MVarId :=
  return (← read).goal

end Aesop
