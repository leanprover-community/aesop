/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta Halkjær From
-/

import Lean

import Aesop.Percent
import Aesop.Rule

open Lean
open Lean.Meta

namespace Aesop

/-! ## Node IDs -/

-- TODO remove?
structure NodeId where
  toNat : Nat
  deriving Inhabited, DecidableEq

namespace NodeId

protected def zero : NodeId :=
  ⟨0⟩

protected def one : NodeId :=
  ⟨1⟩

protected def succ : NodeId → NodeId
  | ⟨n⟩ => ⟨n + 1⟩

instance : LT NodeId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := NodeId) (· < ·) :=
  λ n m => inferInstanceAs (Decidable (n.toNat < m.toNat))

instance : ToFormat NodeId where
  format n := format n.toNat

end NodeId


/-! ## Rule Application IDs -/

-- TODO remove?
structure RappId where
  toNat : Nat
  deriving Inhabited, DecidableEq

namespace RappId

protected def zero : RappId :=
  ⟨0⟩

protected def succ : RappId → RappId
  | ⟨n⟩ => ⟨n + 1⟩

protected def one : RappId :=
  ⟨1⟩

instance : LT RappId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := RappId) (· < ·) :=
  λ n m => inferInstanceAs $ Decidable (n.toNat < m.toNat)

instance : ToFormat RappId where
  format n := format n.toNat

end RappId


/-! ## Nodes and Rule Applications -/

-- Mutual structures are currently unsupported, so we desugar manually.
structure Node' (RappRef : Type) : Type where
  id : NodeId
  parent : Option RappRef
  goal : Expr
  successProbability : Percent
  normalizationProof : Option Expr
  rapps : List RappRef
  failedRapps : List RegularRule
  unsafeQueue : Option (List UnsafeRule)
  isProven : Bool
  isUnprovable : Bool
  isIrrelevant : Bool
  deriving Inhabited

structure Rapp' (NodeRef : Type) : Type where
  id : RappId
  parent : NodeRef
  appliedRule : RegularRule
  successProbability : Percent
  proof : Expr
  subgoals : List NodeRef
  isProven : Bool
  isUnprovable : Bool
  isIrrelevant : Bool
  deriving Inhabited

mutual
  unsafe inductive NodeWrap
    | mkNodeWrap : Node' (IO.Ref RappWrap) → NodeWrap

  unsafe inductive RappWrap
    | mkRappWrap : Rapp' (IO.Ref NodeWrap) → RappWrap
end

structure NodeRappSpec where
  Node : Type
  Rapp : Type
  unfoldNode : Node → Node' (IO.Ref Rapp)
  unfoldRapp : Rapp → Rapp' (IO.Ref Node)

unsafe def NodeRappImp : NodeRappSpec where
  Node := NodeWrap
  Rapp := RappWrap
  unfoldNode | NodeWrap.mkNodeWrap n => n
  unfoldRapp | RappWrap.mkRappWrap r => r

@[implementedBy NodeRappImp]
constant NodeRapp : NodeRappSpec := {
  Node := Unit
  Rapp := Unit
  unfoldNode := λ _ => arbitrary
  unfoldRapp := λ _ => arbitrary
}

def Node : Type := NodeRapp.Node

def Rapp : Type := NodeRapp.Rapp

namespace Node

def unfold (n : Node) : Node' (IO.Ref Rapp) :=
  NodeRapp.unfoldNode n

def id (n : Node) : NodeId :=
  n.unfold.id

end Node

namespace Rapp

def unfold (r : Rapp) : Rapp' (IO.Ref Node) :=
  NodeRapp.unfoldRapp r

end Rapp

end Aesop
