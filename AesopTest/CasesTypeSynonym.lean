import Aesop

inductive T

abbrev U := T

def V := T
abbrev W := V
def X := V

example (h : T) : False := by
  fail_if_success aesop (config := { terminal := true })
  aesop (add safe cases T)

example (h : T) : False := by
  aesop (add safe cases U)

example (h : U) : False := by
  aesop (add safe cases U)

example (h : V) : False := by
  fail_if_success aesop (config := { terminal := true })
  fail_if_success aesop (add safe cases T) (config := { terminal := true })
  fail_if_success aesop (add safe cases U) (config := { terminal := true })
  aesop (add safe cases V)

example (h : W) : False := by
  fail_if_success aesop (config := { terminal := true })
  fail_if_success aesop (add safe cases T) (config := { terminal := true })
  fail_if_success aesop (add safe cases U) (config := { terminal := true })
  aesop (add safe cases V)

example (h : V) : False := by
  aesop (add safe cases W)

example (h : X) : False := by
  fail_if_success aesop (config := { terminal := true })
  fail_if_success aesop (add safe cases T) (config := { terminal := true })
  fail_if_success aesop (add safe cases U) (config := { terminal := true })
  fail_if_success aesop (add safe cases V) (config := { terminal := true })
  fail_if_success aesop (add safe cases W) (config := { terminal := true })
  aesop (add safe cases X)

example (h : T) : False := by
  aesop (add safe cases (transparency! := default) X)

inductive A (α : Type) : Prop

abbrev B β := A β

example (h : A Unit) : False := by
  fail_if_success aesop (config := { terminal := true })
  aesop (add safe cases A)

example (h : A Unit) : False := by
  aesop (add safe cases B)

example (h : B Unit) : False := by
  fail_if_success aesop (config := { terminal := true })
  aesop (add safe cases A)

example (h : B Unit) : False := by
  aesop (add safe cases B)
