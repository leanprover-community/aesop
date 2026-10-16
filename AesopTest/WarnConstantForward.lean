/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

set_option aesop.check.all true

/--
warning: aesop: forward builder: rule has no slots.
Forward rules without slots are rarely useful and are often tagged by mistake.
Use `set_option aesop.warn.constantForward false` to disable this warning.
-/
#guard_msgs in
@[aesop safe forward]
axiom constForward : True

/--
error: aesop: destruct builder: rule has no slots.
Destruct rules without slots cannot clear any hypothesis and are almost certainly a mistake.
-/
#guard_msgs in
@[aesop safe destruct]
axiom constDestruct : True

set_option aesop.warn.constantForward false in
@[aesop safe forward]
axiom constForwardSilent : True
