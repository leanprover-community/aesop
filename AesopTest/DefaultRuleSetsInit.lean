/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

declare_aesop_rule_sets [regular₁, regular₂]

declare_aesop_rule_sets [dflt₁, dflt₂] (default := true)
