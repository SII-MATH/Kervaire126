module

public import KIP126.Def.Algebra.GradedModule.Shift.TensorLine.Raw.Data

@[expose] public section

/-! Compatibility of scalar multiplication with the actual augmentation action. -/

namespace KIP126.Algebra.GradedModule.TensorLine

open CategoryTheory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- The prescribed line multiplication intertwines the shifted trivial action
with the same augmentation action in the sum degree. -/
theorem iso_hom_action {A : Mon (GrVect K)} (ε : Augmentation A) (t u : ℤ) :
    (leftTensorMonad A).map (iso K t u).hom ≫ (trivialAt K ε (t + u)).a =
      ((internalShift K A t).obj (trivialAt K ε u)).a ≫ (iso K t u).hom := by
  open MonoidalCategory in
    set_option backward.isDefEq.respectTransparency false in
      change (A.X ◁ (iso K t u).hom) ≫
          (ε.hom ▷ _) ≫ (λ_ _).hom =
        ((α_ A.X _ _).inv ≫ (((ε.hom ▷ _) ≫ (λ_ _).hom) ▷ _)) ≫
          (iso K t u).hom
      rw [whisker_exchange_assoc]
      dsimp only [Mon.trivial]
      rw [leftUnitor_naturality (iso K t u).hom]
      rw [leftUnitor_tensor_hom, ← Category.assoc, associator_inv_naturality_left_assoc]
      simp only [comp_whiskerRight, Category.assoc]

end KIP126.Algebra.GradedModule.TensorLine
