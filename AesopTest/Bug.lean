import Aesop

example (h : α ∧ β) : α ∧ β := by
  set_option trace.aesop true in
  set_option profiler true in
  aesop (options := { destructProductsTransparency := .default })
