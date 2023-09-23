import Aesop

set_option aesop.check.all true

section buildCheck

/- [1/2] Check aesop.
   Write a simple theorem and try to prove it `by aesop`.
   If the goal is closed (i.e., No goals displayed in the InfoView),
   aesop is likely to have been properly built.
   Additionally, you may try to type `aesop?` to see scripts suggested by aesop.
-/
theorem foo1 (a : Nat) : a + 1 = Nat.succ a := by
  aesop
  -- aesop?

/- [2/2] Check LeanInfer.
   Write a simple theorem and try to prove it `by LeanInfer`.
   If a list of tactics is shown under `Tactic suggestions` in the InfoView
   while the goal is not closed, the LeanInfer part is successfully built as well.
   For the first time, should it ask you to download the model by running `suggest_tactics!`,
   following it will automatically download the model to `~/.cache/lean_infer/` by default, 
   with the path overridable by setting the `LEAN_INFER_CACHE_DIR` environment variable.
-/
theorem foo2 (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  -- suggest_tactics!

end buildCheck
