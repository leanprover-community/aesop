/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean
open Lean.Meta

namespace Aesop

inductive PhaseName
  | norm
  | safe
  | «unsafe»
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace PhaseName

instance : Ord PhaseName where
  compare s₁ s₂ := compare s₁.toCtorIdx s₂.toCtorIdx

instance : ToString PhaseName where
  toString
    | norm => "norm"
    | safe => "safe"
    | «unsafe» => "unsafe"

end PhaseName


inductive ScopeName
  | global
  | «local»
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace ScopeName

instance : Ord ScopeName where
  compare s₁ s₂ := compare s₁.toCtorIdx s₂.toCtorIdx

instance : ToString ScopeName where
  toString
    | global => "global"
    | «local» => "local"

end ScopeName


inductive BuilderName
  | apply
  | cases
  | constructors
  | elim
  | forward
  | simp
  | tactic
  | unfold
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace BuilderName

instance : Ord BuilderName where
  compare b₁ b₂ := compare b₁.toCtorIdx b₂.toCtorIdx

instance : ToString BuilderName where
  toString
    | apply => "apply"
    | cases => "cases"
    | constructors => "constructors"
    | elim => "elim"
    | forward => "forward"
    | simp => "simp"
    | tactic => "tactic"
    | unfold => "unfold"

end BuilderName


-- Rules are identified by a `RuleName` throughout Aesop. We assume that rule
-- names are unique within our 'universe', i.e. within the rule sets that we are
-- working with. All data structures should enforce this invariant.
structure RuleName where
  name : Name
  builder : BuilderName
  phase : PhaseName
  scope : ScopeName
  protected hash : UInt64 :=
    mixHash (hash name) $ mixHash (hash builder) $ mixHash (hash phase)
      (hash scope)
  deriving Inhabited

namespace RuleName

instance : Hashable RuleName where
  hash n := n.hash

instance : BEq RuleName where
  beq n₁ n₂ :=
    n₁.hash == n₂.hash && n₁.builder == n₂.builder && n₁.phase == n₂.phase &&
    n₁.scope == n₂.scope && n₁.name == n₂.name

protected def compare : (_ _ : RuleName) → Ordering :=
  compareLexicographic (compareBy (·.builder)) $
  compareLexicographic (compareBy (·.phase)) $
  compareLexicographic (compareBy (·.scope)) $
  (λ n₁ n₂ => n₁.name.cmp n₂.name)

protected def quickCompare (n₁ n₂ : RuleName) : Ordering :=
  match compare n₁.hash n₂.hash with
  | Ordering.eq => n₁.compare n₂
  | ord => ord

instance : Ord RuleName :=
  ⟨RuleName.compare⟩

instance : ToString RuleName where
  toString n :=
    toString n.phase ++ "|" ++ toString n.builder ++ "|" ++ toString n.scope ++
    "|" ++ toString n.name

end RuleName


inductive RuleIdent
  | const (decl : Name)
  | fvar (userName : Name)
  deriving Inhabited, BEq, Hashable

namespace RuleIdent

instance : ToString RuleIdent where
  toString
    | const decl => toString decl
    | fvar userName => toString userName

def name : RuleIdent → Name
  | const decl => decl
  | fvar userName => userName

def scope : RuleIdent → ScopeName
  | const .. => ScopeName.global
  | fvar .. => ScopeName.local

def type : RuleIdent → MetaM Expr
  | const c => return (← getConstInfo c).type
  | fvar userName => return (← getLocalDeclFromUserName userName).type

def toRuleName (phase : PhaseName) (builder : BuilderName)
    (i : RuleIdent) : RuleName where
  phase := phase
  builder := builder
  scope := i.scope
  name := i.name

end RuleIdent


namespace RuleName

def toRuleIdent (i : RuleName) : RuleIdent :=
  match i.scope with
  | ScopeName.global => RuleIdent.const i.name
  | ScopeName.local => RuleIdent.fvar i.name

end RuleName

end Aesop
