/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Basic
import Aesop.Util.EqualUpToIds
import Aesop.Tree.RunMetaM

-- Some simple test cases for the EqualUpToIds module. The module is mostly
-- tested by using it in script validation, which is run on almost all Aesop
-- calls in the test suite.

open Aesop Lean Lean.Elab.Tactic

def assertEqualTactics (t₁ t₂ : TacticM Unit) : TacticM Unit := do
  let commonMCtx ← getMCtx
  let preState ← show MetaM _ from saveState
  let preGoals ← getGoals
  let (state₁, goals₁) ← runTacticMCapturingPostState t₁ preState preGoals
  let (state₂, goals₂) ← runTacticMCapturingPostState t₂ preState preGoals
  let eq ←
    tacticStatesEqualUpToIds commonMCtx state₁.meta.mctx state₂.meta.mctx
      goals₁.toArray goals₂.toArray
  if ! eq then
    throwError "Tactics produced different tactic states.\nTactic 1:{indentD $ ← ppTacticState state₁ goals₁}\nTactic 2:{indentD $ ← ppTacticState state₂ goals₂}\n"
where
  ppTacticState (state : Meta.SavedState) (goals : List MVarId) :
      MetaM MessageData :=
    state.runMetaM' do
      addMessageContext $ .joinSep (goals.map toMessageData) "\n"

open Lean.Elab.Tactic in
elab &"assert_equal_tactics "
    " { " ts₁:tacticSeq " } " " { " ts₂:tacticSeq " } " : tactic => do
  assertEqualTactics (evalTactic ts₁) (evalTactic ts₂)

example : True := by
  assert_equal_tactics { trivial } { trivial }
  trivial

example : True := by
  assert_equal_tactics { open Classical in trivial } { trivial }
  trivial

/--
error: Tactics produced different tactic states.
Tactic 1:
  case zero
  m : Nat
  ⊢ True
  case succ
  m n✝ : Nat
  ⊢ True
Tactic 2:
  case zero
  n : Nat
  ⊢ True
  case succ n n✝ : Nat ⊢ True
-/
#guard_msgs in
example (n m : Nat) : True := by
  assert_equal_tactics { cases n } { cases m }
  trivial

example : 0 < 3 := by
  apply Nat.lt_trans
  assert_equal_tactics { exact Nat.lt_succ_self 0 } { exact Nat.lt_succ_self 0 }
  (case m => exact 1); all_goals decide

example : 0 < 3 := by
  apply Nat.lt_trans
  assert_equal_tactics { apply Nat.lt_trans } { apply Nat.lt_trans }
  (case m => exact 1); all_goals decide
