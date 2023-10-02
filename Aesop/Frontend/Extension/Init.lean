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
abbrev RuleSetExtension := SimpleScopedEnvExtension RuleSetMember RuleSet

/--
Structure containing information about all declared Aesop rule sets.
-/
structure DeclaredRuleSets where
  ruleSets : HashMap Name RuleSetExtension
  defaultRuleSets : NameSet
  deriving Inhabited

instance : EmptyCollection DeclaredRuleSets :=
  ⟨∅, ∅⟩

initialize declaredRuleSetsRef : IO.Ref DeclaredRuleSets ←
  IO.mkRef ∅

def getDeclaredRuleSets : IO (HashMap RuleSetName RuleSetExtension) :=
  return (← declaredRuleSetsRef.get).ruleSets

def getDefaultRuleSetNames : IO NameSet :=
  return (← declaredRuleSetsRef.get).defaultRuleSets

end Aesop
