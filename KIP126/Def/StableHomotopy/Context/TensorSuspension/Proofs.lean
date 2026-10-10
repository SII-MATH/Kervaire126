import KIP126.Def.StableHomotopy.Context.TensorSuspension.Predicates

namespace KIP126.StableHomotopy

open CategoryTheory MonoidalCategory

attribute [reassoc] RightTensorSuspensionCompatibility.natural_right
  RightTensorSuspensionCompatibility.associator

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [∀ X : C, (tensorRight X).CommShift ℤ]

/-- Moving an arbitrary suspended-output map through a tensor pairing.
This is the structural one-sided boundary calculation, before any Adams
objects or triangle-completion choices are introduced. -/
theorem rightTensorSuspension_pairing
    (h : RightTensorSuspensionCompatibility (C := C))
    {H B X Y Z : C} (δ : H ⟶ B⟦(1 : ℤ)⟧) (f : X ⊗ Y ⟶ Z) :
    (α_ H X Y).hom ≫ H ◁ f ≫ (δ ▷ Z) ≫
        (Functor.commShiftIso (tensorRight Z) (1 : ℤ)).hom.app B =
      (((δ ▷ X) ≫ (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app B) ▷ Y) ≫
        (Functor.commShiftIso (tensorRight Y) (1 : ℤ)).hom.app (B ⊗ X) ≫
        ((α_ B X Y).hom ≫ B ◁ f)⟦(1 : ℤ)⟧' := by
  rw [whisker_exchange_assoc, ← associator_naturality_left_assoc]
  erw [h.natural_right, h.associator_assoc]
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]
  erw [Category.assoc, Category.assoc]
  rfl

end KIP126.StableHomotopy
