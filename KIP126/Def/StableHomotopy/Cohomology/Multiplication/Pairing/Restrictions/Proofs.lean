import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory BraidedCategory KIP126.Classical.Adams

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- With a unit in the right input, the coefficient product is just
reassociation followed by tensoring the specified map with HF2. -/
theorem mod2CoefficientPairing_unit_right {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((H.HF2 ⊗ X) ◁ adamsUnit H.unit Y) ≫ mod2CoefficientPairing H R f =
      (α_ H.HF2 X Y).hom ≫ H.HF2 ◁ f := by
  have hcoh :
      ((H.HF2 ⊗ X) ◁ (λ_ Y).inv) ≫ tensorμ H.HF2 X (𝟙_ C) Y ≫
        ((ρ_ H.HF2).hom ▷ (X ⊗ Y)) = (α_ H.HF2 X Y).hom := by
    simp only [tensorμ, braiding_tensorUnit_right, whiskerLeft_comp, comp_whiskerRight]
    monoidal
  letI := R.monoid
  unfold mod2CoefficientPairing adamsUnit
  rw [whiskerLeft_comp, Category.assoc, ← tensorHom_id, tensorμ_natural_right_assoc]
  rw [tensorHom_comp_tensorHom]
  simp only [whiskerLeft_id, Category.id_comp, ← R.one_eq, MonObj.mul_one]
  rw [tensorHom_def, ← Category.assoc, ← Category.assoc]
  rw [Category.assoc _ (tensorμ H.HF2 X (𝟙_ C) Y), hcoh]

/-- With a unit in the left input, one moves the remaining coefficient
past X and then tensors the specified map with HF2. The formula retains
the actual braiding and does not impose a separate commutativity hypothesis. -/
theorem mod2CoefficientPairing_unit_left {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    (adamsUnit H.unit X ▷ (H.HF2 ⊗ Y)) ≫ mod2CoefficientPairing H R f =
      (α_ X H.HF2 Y).inv ≫ ((β_ X H.HF2).hom ▷ Y) ≫
        (α_ H.HF2 X Y).hom ≫ H.HF2 ◁ f := by
  have hcoh :
      ((λ_ X).inv ▷ (H.HF2 ⊗ Y)) ≫ tensorμ (𝟙_ C) X H.HF2 Y ≫
        ((λ_ H.HF2).hom ▷ (X ⊗ Y)) =
      (α_ X H.HF2 Y).inv ≫ ((β_ X H.HF2).hom ▷ Y) ≫
        (α_ H.HF2 X Y).hom := by
    simp only [tensorμ]
    monoidal
  letI := R.monoid
  unfold mod2CoefficientPairing adamsUnit
  rw [comp_whiskerRight, Category.assoc, ← tensorHom_id H.unit X,
    tensorμ_natural_left_assoc]
  rw [tensorHom_comp_tensorHom]
  simp only [id_whiskerRight, Category.id_comp, ← R.one_eq, MonObj.one_mul]
  rw [tensorHom_def, ← Category.assoc, ← Category.assoc]
  rw [Category.assoc _ (tensorμ (𝟙_ C) X H.HF2 Y), hcoh]
  simp only [Category.assoc]

end KIP126.StableHomotopy.Cohomology
