/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.RuleSet.Member
import Aesop.RuleSet.Name

open Lean

namespace Aesop

structure RuleNameFilter where
  ident : RuleIdent
  /--
  `#[]` means 'match any builder'
  -/
  builders : Array BuilderName
  /--
  `#[]` means 'match any phase'
  -/
  phases : Array PhaseName

namespace RuleNameFilter

def ofIdent (i : RuleIdent) : RuleNameFilter where
  ident := i
  builders := #[]
  phases := #[]

def matchesPhase (f : RuleNameFilter) (p : PhaseName) : Bool :=
  f.phases.isEmpty || f.phases.contains p

def matchesBuilder (f : RuleNameFilter) (b : BuilderName) : Bool :=
  f.builders.isEmpty || f.builders.contains b

def «matches» (f : RuleNameFilter) (n : RuleName) : Bool :=
  f.ident.name == n.name &&
  f.ident.scope == n.scope &&
  f.matchesPhase n.phase &&
  f.matchesBuilder n.builder

def matchesSimpTheorem? (f : RuleNameFilter) : Option Name := Id.run do
  if let .const decl := f.ident then
    if f.matchesBuilder .simp then
      return some decl
  return none

def matchesLocalNormSimpRule? (f : RuleNameFilter) :
    Option LocalNormSimpRule := Id.run do
  if let .fvar fvarUserName := f.ident then
    if f.matchesBuilder .simp then
      return some { fvarUserName }
  return none

end RuleNameFilter


structure RuleSetNameFilter where
  ns : Array RuleSetName -- #[] means 'match any rule set'

namespace RuleSetNameFilter

protected def all : RuleSetNameFilter :=
  ⟨#[]⟩

def matchesAll (f : RuleSetNameFilter) : Bool :=
  f.ns.isEmpty

def «matches» (f : RuleSetNameFilter) (n : RuleSetName) : Bool :=
  f.matchesAll || f.ns.contains n

def matchedRuleSetNames (f : RuleSetNameFilter) : Option (Array RuleSetName) :=
  if f.matchesAll then none else some f.ns

end Aesop.RuleSetNameFilter
