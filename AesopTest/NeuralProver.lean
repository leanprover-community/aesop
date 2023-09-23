import Aesop

set_option aesop.check.all true

section simpleTest

structure neuralConfig where
  neuralProver : String

@[aesop unsafe 50% neural]
def conf : neuralConfig := { neuralProver := "onnx-leandojo-lean4-tacgen-byt5-small" }

theorem foo (a: Nat) : a + 1 = Nat.succ a := by
  aesop

end simpleTest
