import Aesop

set_option aesop.check.all true

-- TODO simp_all introduces spurious metavariables in this example
set_option aesop.check.rules false
set_option aesop.check.tree false

-- TODO broken due to lean4#4251
set_option aesop.check.script false
set_option aesop.check.script.steps false

theorem foo {a : Nat → Nat} (ha : a 0 = 37) :
    (match h : a 0 with | 42 => by simp_all | n => n) = 37 := by
  aesop
