import Aesop

set_option aesop.check.all true

abbrev State := String → Int

inductive Com where
| Skip : Com
| Seq : Com → Com → Com

declare_syntax_cat com

syntax "SKIP" : com
syntax com ";" com : com
syntax "(" com ")" : com
syntax term : com

syntax "[Com|" com "]" : term

macro_rules
| `([Com| SKIP]) => `(Com.Skip)
| `([Com| $x ; $y]) => `(Com.Seq [Com| $x] [Com| $y])
| `([Com| ( $x:com )]) => `([Com| $x])
| `([Com| $x:term ]) => `($x)

@[aesop safe]
inductive BigStep : Com → State → State → Prop where
| Skip : BigStep Com.Skip s s
| Seq (h1 : BigStep c₁ s t) (h2 : BigStep c₂ t u) : BigStep [Com| c₁;c₂] s u

namespace BigStep

@[aesop norm elim]
theorem Seq_inv (h : BigStep [Com| c₁;c₂] s u) :
    ∃ t, BigStep c₁ s t ∧ BigStep c₂ t u :=
  match h with
  | Seq (t := t) h₁ h₂ => ⟨t, h₁, h₂⟩

end BigStep

theorem seq_assoc :
    BigStep [Com| (c1;c2);c3] s s' ↔ BigStep [Com| c1;c2;c3] s s' := by
  aesop
