import KIP126.Def.ClassicalAdams.Moss.Composition.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Proofs
import KIP126.Def.StableHomotopy.Context.Mapping.Composition.Proofs

namespace KIP126.Classical.Adams.Moss

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- In filtration zero the construction is exactly the selected closed
composition, not merely an unrelated map with the same endpoints. -/
@[simp] theorem smashComposition_zero (X Y Z : C) :
    smashComposition unit X Y Z 0 0 = Mapping.composition X Y Z := by
  simp only [smashComposition, adamsSmashSphereTensorIso,
    adamsSmashSpherePairingIso_zero, adamsSmashTower]
  have h : tensorμ (𝟙_ C) (mappingObject X Y) (𝟙_ C) (mappingObject Y Z) ≫
        ((λ_ (𝟙_ C)).hom ⊗ₘ Mapping.composition X Y Z) ≫
        (λ_ (mappingObject X Z)).hom =
      ((λ_ (mappingObject X Y)).hom ⊗ₘ (λ_ (mappingObject Y Z)).hom) ≫
        Mapping.composition X Y Z := by
    simp only [tensorHom_def, Category.assoc]
    rw [leftUnitor_naturality]
    simpa only [tensorHom_def, Category.assoc] using
      (leftUnitor_monoidal_assoc (mappingObject X Y) (mappingObject Y Z)
        (Mapping.composition X Y Z)).symm
  rw [h, ← Category.assoc, tensorHom_comp_tensorHom]
  simp

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- The actual-stage map is tied to the same concrete smash construction by
the already chosen exactness comparisons. -/
theorem stageComposition_comparison (X Y Z : C) (s t : ℕ) :
    stageComposition unit X Y Z s t ≫
        (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).hom =
      ((adamsTowerSmashIso unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) ≫
        smashComposition unit X Y Z s t := by
  simp only [stageComposition, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp] theorem stageComposition_zero (X Y Z : C) :
    stageComposition unit X Y Z 0 0 = Mapping.composition X Y Z := by
  simp only [stageComposition, adamsTowerSmashIso, Iso.refl_hom, Iso.refl_inv,
    smashComposition_zero]
  change (𝟙 (mappingObject X Y) ⊗ₘ 𝟙 (mappingObject Y Z)) ≫
    Mapping.composition X Y Z ≫ 𝟙 (mappingObject X Z) = _
  simp

/-- At stage zero the mapping-tower construction composes actual maps under
the chosen adjunction. -/
theorem stageComposition_zero_name {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (λ_ (𝟙_ C)).inv ≫ (Mapping.name f ⊗ₘ Mapping.name g) ≫
        stageComposition unit X Y Z 0 0 = Mapping.name (f ≫ g) := by
  rw [stageComposition_zero]
  exact Mapping.composeNames_name f g

end
end KIP126.Classical.Adams.Moss
