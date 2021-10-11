/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Percent

namespace Aesop

def unificationGoalPenalty : Percent :=
  Percent.ofNat 80 |>.get!

end Aesop
