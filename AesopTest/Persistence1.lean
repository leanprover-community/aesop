/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import AesopTest.Persistence0

set_option aesop.check.all true

namespace Aesop

@[aesop 50% constructors (rule_sets [test_persistence1])]
inductive NatOrBool where
  | ofNat (n : Nat)
  | ofBool (b : Bool)

example (b : Bool) : NatOrBool := by
  aesop (rule_sets [test_persistence1])

end Aesop
