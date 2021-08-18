import Aesop

open Aesop
open Lean
open Lean.Meta

def applyRule (e : Expr) (input : RuleTacInput) : MetaM RuleTacOutput := do
  let goals ← apply input.goal e
  UserRuleTacOutput.toRuleTacOutput { regularGoals := goals.toArray }

def applyHyps : RuleTac := λ input =>
  withMVarContext input.goal do
    let lctx ← getLCtx
    let mut outputs := #[]
    for h in lctx do
        if h.isAuxDecl then continue
        let initialState ← saveState
        try
          let output ← applyRule (mkFVar h.fvarId) input
          outputs := outputs.push output
        catch _ => continue
        finally restoreState initialState
    return outputs

example (Even : Nat → Prop) (zero : Even 0)
    (plusTwo : ∀ n, Even n → Even (n + 2)) :
    Even 8 := by
  aesop (unsafe [applyHyps 50%])
