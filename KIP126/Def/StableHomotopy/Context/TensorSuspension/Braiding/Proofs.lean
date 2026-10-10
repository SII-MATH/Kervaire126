import KIP126.Def.StableHomotopy.Context.TensorSuspension.Braiding.Predicates

namespace KIP126.StableHomotopy

open CategoryTheory MonoidalCategory BraidedCategory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [BraidedCategory C]

/-- Exchange the tower input past the whole coefficient input, compensating
by the inverse braiding before the original pairing. No symmetry or
commutativity of the pairing is asserted. -/
theorem braidedTensorPairing_swap {H X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    (β_ X (H ⊗ Y)).hom ≫ (α_ H Y X).hom ≫ H ◁ ((β_ X Y).inv ≫ f) =
      (α_ X H Y).inv ≫ ((β_ X H).hom ▷ Y) ≫ (α_ H X Y).hom ≫ H ◁ f := by
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id_assoc]

variable [∀ X : C, (tensorRight X).CommShift ℤ]
  [∀ X : C, (tensorLeft X).CommShift ℤ]

/-- Moving a boundary through the braiding retains the braiding on the
fiber-level map. Dropping that final braiding is not a coherence identity. -/
theorem braidedSuspension_transport
    (h : TensorSuspensionBraidingCompatibility (C := C))
    (X : C) {Y B Z : C} (d : Y ⟶ B⟦(1 : ℤ)⟧) (k : B ⊗ X ⟶ Z) :
    (β_ X Y).hom ≫ (d ▷ X) ≫
        (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app B ≫ k⟦(1 : ℤ)⟧' =
      (X ◁ d) ≫ (Functor.commShiftIso (tensorLeft X) (1 : ℤ)).hom.app B ≫
        ((β_ X B).hom ≫ k)⟦(1 : ℤ)⟧' := by
  rw [← braiding_naturality_right_assoc]
  erw [← Category.assoc (β_ X (B⟦(1 : ℤ)⟧)).hom, h X B]
  simp only [Functor.map_comp]
  exact congrArg (fun f => (X ◁ d) ≫ f) (Category.assoc _ _ _)

end KIP126.StableHomotopy
