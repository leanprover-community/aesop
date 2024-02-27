/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

/--
error: 'noSuchOption' is not a field of structure 'Aesop.Options'
-/
#guard_msgs in
example : True := by
  aesop (config := { noSuchOption := true })

/--
error: 'noSuchOption' is not a field of structure 'Lean.Meta.Simp.ConfigCtx'
-/
#guard_msgs in
example : True := by
  aesop (simp_config := { noSuchOption := true })
