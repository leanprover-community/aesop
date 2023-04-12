import Aesop

example : True := by
  set_option trace.aesop true in
  set_option profiler true in
  aesop (options := { destructProductsTransparency := .default })
