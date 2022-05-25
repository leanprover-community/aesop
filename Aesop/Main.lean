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

@[tactic Frontend.Parser.aesopTactic]
def evalAesop : Tactic := λ stx =>
  withMainContext do
    let (profile, totalTime) ← IO.time do
      let (config, configParseTime) ← IO.time $ Frontend.TacticConfig.parse stx
      let profile := { Profile.empty with configParsing := configParseTime }
      let (profile, searchTime) ← IO.time $
        liftMetaTacticAux λ goal => do
          let ((goal, ruleSet), ruleSetConstructionTime) ← IO.time $
            config.getRuleSet goal
          let profile := { profile with ruleSetConstruction := ruleSetConstructionTime }
          aesop_trace[ruleSet] "Rule set:{indentD $ toMessageData ruleSet}"
          let profile ← bestFirst goal ruleSet config.options profile
          return (profile, [])
      pure { profile with search := searchTime }
    let profile := { profile with total := totalTime }
    aesop_trace[profile] toMessageData profile

end Aesop
