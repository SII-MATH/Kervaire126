import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Boundary.Right.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]
  [∀ Y : C, (tensorLeft Y).CommShift ℤ] [MonoidalPreadditive C]

/-- Evaluate the actual second-input boundary formula on two represented
maps. Taking A and B to be spheres gives the input used for homotopy products;
it does not test the whole layer spectrum against arbitrary maps. -/
theorem adamsSphereLayerProduct_ι_left_δ_representatives
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ)
    {A B : C} (x : A ⟶ adamsTower H.unit (𝟙_ C) s)
    (y : B ⟶ adamsLayerAt H.unit (𝟙_ C) t) :
    ((((x ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂) ⊗ₘ y) ≫
        adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃) =
      (x ⊗ₘ (y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃)) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧' := by
  have hin : ((x ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂) ⊗ₘ y) =
      (x ⊗ₘ y) ≫ ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ▷
        adamsLayerAt H.unit (𝟙_ C) t) := by
    have ht {U V W Z Q : C} (a : U ⟶ V) (b : W ⟶ Z) (f : V ⟶ Q) :
        ((a ≫ f) ⊗ₘ b) = (a ⊗ₘ b) ≫ (f ▷ Z) := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
    exact ht x y _
  have hout : (x ⊗ₘ y) ≫
      (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) =
      x ⊗ₘ (y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [hin]
  simp only [Category.assoc]
  erw [adamsSphereLayerProduct_ι_left_δ H R h hb]
  erw [← Category.assoc (x ⊗ₘ y), hout]
  rfl

/-- For these two representatives, only their own precomposition of the
ordered-successor defect must vanish. The global morphism-level vanishing
criterion is stronger and is not imposed as a premise here. -/
theorem adamsSphereLayerProduct_ι_left_δ_representatives_ordered_iff
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ)
    {A B : C} (x : A ⟶ adamsTower H.unit (𝟙_ C) s)
    (y : B ⟶ adamsLayerAt H.unit (𝟙_ C) t) :
    (((((x ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂) ⊗ₘ y) ≫
        adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃) =
      (x ⊗ₘ (y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃)) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingNextRight H.unit s t)⟦(1 : ℤ)⟧') ↔
      (x ⊗ₘ (y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃)) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t -
          adamsTowerSpherePairingNextRight H.unit s t)⟦(1 : ℤ)⟧' = 0 := by
  have hsub {U V W Z : C} (a : U ⟶ V) (b : V ⟶ W⟦(1 : ℤ)⟧) (f g : W ⟶ Z) :
      (a ≫ b ≫ f⟦(1 : ℤ)⟧' = a ≫ b ≫ g⟦(1 : ℤ)⟧') ↔
        a ≫ b ≫ (f - g)⟦(1 : ℤ)⟧' = 0 := by
    simp only [Functor.map_sub, Preadditive.comp_sub, sub_eq_zero]
  have hp := adamsSphereLayerProduct_ι_left_δ_representatives H R h hb s t x y
  constructor
  · intro he
    exact (hsub _ _ _ _).mp (hp.symm.trans he)
  · intro hz
    exact hp.trans ((hsub _ _ _ _).mpr hz)

end
end KIP126.Classical.Adams
