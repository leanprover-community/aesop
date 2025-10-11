import Aesop

-- Fix a problem where each rule would only try to synthInstance one per goal.

set_option aesop.dev.statefulForward false

namespace test₁

axiom myProp {A : Type} {B : Type} (a : A) (b : B) : Prop

class myClass (A : Type) (B : Type) where
  data (a : A) (b : B) : Type

axiom myThm {A : Type} {B : Type} (a : A) (b : B)  [myClass A B] : myProp a b

example {A : Type} {B : Type} (a : A) (b : B) [myClass A B] : myProp a b := by
  saturate [myThm]
  assumption

end test₁

namespace test₃

universe u₁ u₂ u₃ u₄

axiom myProp {A : Type u₁} {B : Type u₂} (a : A) (b : B) : Prop

class myClass (A : Type u₁) (B : Type u₂) where
  data (a : A) (b : B) : Type u₄

axiom myThm {A : Type u₁} {B : Type u₂} [myClass A B] (a : A) (b : B) : myProp a b

example {A : Type u₁} {B : Type u₂} {C : Type u₃} [myClass A B]
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : A) (b₁ b₂ b₃ b₄ b₅ b₇ b₈ : B) (c₁ c₂ c₃ : C) :
    myProp a₁ b₁ := by
  saturate [myThm]
  assumption

end test₃
