import KIP126.Def.Algebra.GradedComodule.LeftTensor.Data

/-! Properties of the prescribed left-tensored coaction. -/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem leftTensorCoaction_counit (C : Comon V) (X : V) (A : RightComodule C) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).ε.app (X ⊗ A.A) =
      𝟙 (X ⊗ A.A) := by
  sorry

theorem leftTensorCoaction_coassoc (C : Comon V) (X : V) (A : RightComodule C) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).δ.app (X ⊗ A.A) =
      leftTensorCoaction C X A ≫
        (rightTensorComonad C).map (leftTensorCoaction C X A) := by
  sorry

theorem leftTensorCoaction_map (C : Comon V) (X : V) {A B : RightComodule C}
    (f : A ⟶ B) :
    leftTensorCoaction C X A ≫ (rightTensorComonad C).map (X ◁ f.f) =
      (X ◁ f.f) ≫ leftTensorCoaction C X B := by
  sorry

end KIP126.Algebra.GradedComodule
