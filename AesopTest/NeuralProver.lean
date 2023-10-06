import Aesop

-- set_option aesop.check.all true
-- set_option trace.aesop.tree true
-- set_option trace.aesop true  
-- all three flags are for debugging purpose, not necessarily needed.
set_option maxHeartbeats 0 -- disable timeout

section simpleTest

@[aesop unsafe 50% neural]

/- [1/2] Simple theorem.
   The raw white-box aesop should be able to prove this theorem.
   Since we mark the neural prover as `unsafe`, when the `safe` builtin rules of aesop
   can already prove the goal, our additional option of `neural` will never be called.
   In other words, the theorems that can be proved by the original `aesop` 
   is a strict subset of that can be proved by our `LLM-aesop`. -/
theorem foo1 (a: Nat) : a + 1 = Nat.succ a := by
  aesop

/- [2/2] Hard theorem.
   The raw white-box `aesop` should not be able to prove this theorem.
   After trying all builtin rules, which should all fail on this theorem,
   the original `aesop` will fail to close this goal,
   while our `LLM-aesop` will try the `unsafe` neural prover,
   which can usually prove the goal.
   Note that this is not guaranteed for each time you run `LLM-aesop`,
   as there is existing uncertainty rooted in any machine learning method. -/
theorem foo2 (a b c : Nat) : a + b + c = c + b + a := by
  aesop

end simpleTest
