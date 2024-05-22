import Aesop

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
a b : Nat
⊢ a + b = b + 2 * a
-/
#guard_msgs in
example : ∀ (a b : Nat), a + b = b + 2 * a := by aesop (config := { terminal := true })
