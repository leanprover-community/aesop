import Aesop

set_option aesop.check.all true

open Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "aesop_intros" : tactic =>
  liftMetaTactic λ mvarId => do
    let (_, mvarId) ← Aesop.BuiltinRules.introsUnfolding mvarId
    return [mvarId]

structure SimpleGraph' (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {x y}, Adj x y → Adj y x := by aesop_intros

def SimpleGraph.Sigma {ι : Type u} {V : ι → Type v} (G : (i : ι) → SimpleGraph' (V i)) :
  SimpleGraph' (Σ i, V i) where
    Adj := fun | \
    symm := _
