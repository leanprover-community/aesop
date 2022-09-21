/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

namespace Aesop

structure Nanos where
  nanos : Nat
  deriving Inhabited, BEq, Ord

namespace Nanos

instance : OfNat Nanos n where
  ofNat := ⟨n⟩

instance : Add Nanos where
  add n m := ⟨n.nanos + m.nanos⟩

def printAsMillis (n : Nanos) : String :=
  let str := toString (n.nanos.toFloat / 1000000)
  match str.split λ c => c == '.' with
  | [beforePoint] => beforePoint ++ "ms"
  | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 3 ++ "ms"
  | _ => unreachable!

end Aesop.Nanos
