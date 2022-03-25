/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Search.Main
import Aesop.BuiltinRules -- ensures that the builtin rules are registered
import Aesop.Frontend.Tactic
import Aesop.Profiling
import Lean

open Lean
open Lean.Elab.Tactic

namespace Aesop

@[tactic Frontend.Parser.aesopTactic]
def evalAesop : Tactic := λ stx =>
  withMainContext do
    let (config, configParseTime) ← IO.time $ Frontend.TacticConfig.parse stx
    let (ruleSet, ruleSetConstructionTime) ← IO.time $
      liftMetaTacticAux λ goal => do
        let (goal, ruleSet) ← config.getRuleSet goal
        return (ruleSet, [goal])
    aesop_trace[ruleSet] "Rule set:{indentD $ toMessageData ruleSet}"
    let (err?, searchTime) ← IO.time $
      try
        bestFirst ruleSet config.options
        return none
      catch e =>
        return some e
    aesop_trace[profile] toMessageData
      { configParsing := configParseTime
        ruleSetConstruction := ruleSetConstructionTime
        search := searchTime
        : ProfilingTimes }
    if let (some err) := err? then
      throw err

end Aesop
