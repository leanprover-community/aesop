import Aesop.Util.EqualUpToIds
import Lean.Elab.Command

open Aesop Lean

run_meta do
  let a := Level.mvar ⟨`a⟩
  let b := Level.mvar ⟨`b⟩
  let x := Level.mvar ⟨`x⟩
  let y := Level.mvar ⟨`y⟩
  let check := fun lhs rhs expected => do
    let result ← (EqualUpToIds.levelsEqualUpToIdsCore lhs rhs).run none {} {} false
    unless result == expected do
      throwError "unexpected universe ID comparison: {lhs}, {rhs}: {result}"
  check (.max a b) (.max x y) true
  check (.max a a) (.max x x) true
  check (.max a b) (.max x x) false
  check (.max a a) (.max x y) false
  -- Pointer-identical sublevels must still register their metavariable mapping.
  check (.max a b) (.max a a) false
  check (.max a a) (.max a b) false
