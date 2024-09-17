/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Meta.Basic

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
  | destruct
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
    | destruct => "destruct"
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
  compareLex (compareOn (·.builder)) $
  compareLex (compareOn (·.phase)) $
  compareLex (compareOn (·.scope)) $
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

def getRuleNameForExpr : Expr → MetaM Name
  | .const decl _ => return decl
  | .fvar fvarId => return (← fvarId.getDecl).userName
  | _ => mkFreshId


inductive DisplayRuleName
  | ruleName (n : RuleName)
  | normSimp
  | normUnfold
  deriving Inhabited, BEq, Ord, Hashable

namespace DisplayRuleName

instance : Coe RuleName DisplayRuleName :=
  ⟨DisplayRuleName.ruleName⟩

instance : ToString DisplayRuleName where
  toString
    | ruleName n => toString n
    | normSimp => "<norm simp>"
    | normUnfold => "<norm unfold>"

end Aesop.DisplayRuleName
