/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleSet

open Lean

namespace Aesop

/--
An environment extension containing an Aesop rule set. Each rule set has its
own extension.
-/
abbrev RuleSetExtension :=
  SimpleScopedEnvExtension BaseRuleSetMember BaseRuleSet

/--
Structure containing information about all declared Aesop rule sets.
-/
structure DeclaredRuleSets where
  /--
  The collection of declared rule sets. Each rule set has an extension, the
  name of the associated `SimpExtension` and the name of the associated
  `SimprocExtension`. The two simp extensions are expected to be declared.
  -/
  ruleSets : Std.HashMap RuleSetName (RuleSetExtension × Name × Name)
  /--
  The set of Aesop rule sets that are enabled by default.
  -/
  defaultRuleSets : Std.HashSet RuleSetName
  deriving Inhabited

instance : EmptyCollection DeclaredRuleSets :=
  ⟨∅, ∅⟩

initialize declaredRuleSetsRef : IO.Ref DeclaredRuleSets ←
  IO.mkRef ∅

def getDeclaredRuleSets : IO (Std.HashMap RuleSetName (RuleSetExtension × Name × Name)) :=
  return (← declaredRuleSetsRef.get).ruleSets

def getDefaultRuleSetNames : IO (Std.HashSet Name) :=
  return (← declaredRuleSetsRef.get).defaultRuleSets

end Aesop
