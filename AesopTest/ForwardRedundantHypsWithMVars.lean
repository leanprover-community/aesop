/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho, Jannis Limperg
-/

-- Regression test for a failure of the `forward` rule builder to realise that
-- it had already added certain hypotheses. The `saturate` loop below adds the
-- same hyp over and over again, only with different level mvars. Thanks to Son
-- Ho for providing this test case.

import Aesop

set_option aesop.check.all true

axiom len {α} (ls : List α) : Int

@[aesop safe forward (pattern := len ls)]
axiom len_pos {α} {ls : List α} : 0 ≤ len (ls : List α)

/--
error: unsolved goals
a : Type u_1
l : List a
fwd : 0 ≤ len l
⊢ 0 ≤ len l
-/
#guard_msgs in
example (l: List a): 0 ≤ len l := by
  saturate
