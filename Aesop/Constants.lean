/-
Copyright <redacted>
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <redacted>
-/

import Aesop.Percent

namespace Aesop

def unificationGoalPenalty : Percent :=
  ⟨0.8⟩

def postponedSafeRuleSuccessProbability : Percent :=
  ⟨0.9⟩

end Aesop
