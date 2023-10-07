/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Frontend.Attribute

namespace Aesop.BuiltinRules

open Lean Lean.Meta

def unhygienicExt (goal : MVarId) : MetaM (Array MVarId) :=
  unhygienic do
    let (_, subgoals) ←
      Std.Tactic.Ext.extCore goal [] (failIfUnchanged := true) |>.run' {}
    return subgoals.map (·.fst)

def unhygienicExtWithScript (goal : MVarId) (generateScript : Bool) :
    MetaM (Array MVarId × Option RuleTacScriptBuilder) := do
  let subgoals ← unhygienicExt goal
  let scriptBuilder? :=
    mkScriptBuilder? generateScript (.unhygienicExt subgoals.size)
  return (subgoals, scriptBuilder?)

@[aesop 80% (rule_sets [builtin])]
def ext : RuleTac := RuleTac.ofSingleRuleTac λ input =>
  unhygienicExtWithScript input.goal input.options.generateScript

end Aesop.BuiltinRules
