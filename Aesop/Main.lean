/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Main
import Aesop.BuiltinRules -- ensures that the builtin rules are registered
import Aesop.Frontend.Tactic
import Aesop.Profiling

open Lean
open Lean.Elab.Tactic

namespace Aesop

@[tactic Frontend.Parser.aesopTacticNoCheckpoint, tactic Frontend.Parser.aesopTacticNoCheckpoint?]
def evalAesop : Tactic := λ stx => do
  profileitM Exception "aesop" (← getOptions) do
  withMainContext do
    let (profile, totalTime) ← IO.time do
      let (config, configParseTime) ← IO.time $ Frontend.TacticConfig.parse stx
      let profile := { Profile.empty with configParsing := configParseTime }
      let goal ← getMainGoal
      let ((goal, ruleSet), ruleSetConstructionTime) ← IO.time $
        config.getRuleSet goal
      let profile :=
        { profile with ruleSetConstruction := ruleSetConstructionTime }
      withConstAesopTraceNode .ruleSet (return "Rule set") do
        ruleSet.trace .ruleSet
      let (profile, searchTime) ← IO.time do
        let (goals, profile) ←
          search goal ruleSet config.options config.simpConfig
            config.simpConfigSyntax? profile
        replaceMainGoal goals.toList
        pure profile
      pure { profile with search := searchTime }
    let profile := { profile with total := totalTime }
    profile.trace .profile

macro_rules
  | `(tactic| aesop $cs:Aesop.tactic_clause*) =>
    `(tactic| checkpoint aesop_no_checkpoint $cs:Aesop.tactic_clause*)
  | `(tactic| aesop? $cs:Aesop.tactic_clause*) =>
    `(tactic| checkpoint aesop_no_checkpoint? $cs:Aesop.tactic_clause*)

end Aesop
