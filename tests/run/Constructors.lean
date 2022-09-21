/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop

set_option aesop.check.all true

inductive Even : Nat → Type
| zero : Even 0
| plusTwo : Even n → Even (n + 2)

attribute [aesop safe] Even

example : Even 6 := by
  aesop
