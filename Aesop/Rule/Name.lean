/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util

open Lean

namespace Aesop.RuleName

inductive Phase
  | norm
  | safe
  | «unsafe»
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace Phase

instance : Ord Phase where
  compare s₁ s₂ := compare s₁.toCtorIdx s₂.toCtorIdx

instance : ToString Phase where
  toString
    | norm => "norm"
    | safe => "safe"
    | «unsafe» => "unsafe"

end Phase

inductive Scope
  | global
  | «local»
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace Scope

instance : Ord Scope where
  compare s₁ s₂ := compare s₁.toCtorIdx s₂.toCtorIdx

instance : ToString Scope where
  toString
    | global => "global"
    | «local» => "local"

end Scope

inductive Builder
  | apply
  | cases
  | constructors
  | forward
  | normDefault
  | safeDefault
  | simp
  | tactic
  | unfold
  | unsafeDefault
  deriving Inhabited, BEq, Hashable
  -- NOTE: Constructors should be listed in alphabetical order for the Ord
  -- instance.

namespace Builder

instance : Ord Builder where
  compare b₁ b₂ := compare b₁.toCtorIdx b₂.toCtorIdx

instance : ToString Builder where
  toString
    | apply => "apply"
    | cases => "cases"
    | constructors => "constructors"
    | forward => "forward"
    | normDefault => "norm_default"
    | safeDefault => "safe_default"
    | simp => "simp"
    | tactic => "tactic"
    | unfold => "unfold"
    | unsafeDefault => "unsafe_default"

end RuleName.Builder

-- Rules are identified by a `RuleName` throughout Aesop. We assume that rule
-- names are unique within our 'universe', i.e. within the rule sets that we are
-- working with. All data structures should enforce this invariant.
structure RuleName where
  ident : Name
  builder : RuleName.Builder
  phase : RuleName.Phase
  scope : RuleName.Scope
  protected hash : UInt64 :=
    mixHash (hash ident) $ mixHash (hash builder) $ mixHash (hash phase)
      (hash scope)
  deriving Inhabited

namespace RuleName

instance : Hashable RuleName where
  hash n := n.hash

instance : BEq RuleName where
  beq n₁ n₂ :=
    n₁.hash == n₂.hash && n₁.builder == n₂.builder && n₁.phase == n₂.phase &&
    n₁.scope == n₂.scope && n₁.ident == n₂.ident

protected def compare : (_ _ : RuleName) → Ordering :=
  Ordering.compareLexicographic (compareBy (·.builder)) $
  Ordering.compareLexicographic (compareBy (·.phase)) $
  Ordering.compareLexicographic (compareBy (·.scope)) $
  (λ n₁ n₂ => n₁.ident.cmp n₂.ident)

protected def quickCompare (n₁ n₂ : RuleName) : Ordering :=
  match compare n₁.hash n₂.hash with
  | Ordering.eq => n₁.compare n₂
  | ord => ord

instance : Ord RuleName :=
  ⟨RuleName.compare⟩

instance : ToString RuleName where
  toString n :=
    toString n.phase ++ "|" ++ toString n.builder ++ "|" ++ toString n.scope ++
    "|" ++ toString n.ident

end RuleName
