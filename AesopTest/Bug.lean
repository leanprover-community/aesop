import Aesop

@[aesop safe constructors]
structure Sig (α : Sort u) (β : α → Sort v) : Sort _ where
  fst : α
  snd : β fst

def T α β := α ∧ β

example (h : T α β) : Sig α (λ _ => β) := by
  aesop (options := { destructProductsTransparency := .default })
