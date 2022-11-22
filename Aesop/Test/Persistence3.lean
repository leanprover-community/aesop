/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Test.Persistence1
import Aesop.Test.Persistence2

namespace Aesop

@[aesop 50% (rule_sets [persistence2])]
def test (b : Bool) : NatOrBool := by
  aesop (rule_sets [persistence1])

end Aesop
