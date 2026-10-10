import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

@[simp] theorem adamsSphereLayerPairingTriangleIso_hom₁ (s t : ℕ) :
    (adamsSphereLayerPairingTriangleIso unit s t).hom.hom₁ =
      (adamsTowerSpherePairingIso unit (s + 1) t).hom := by
  simp only [adamsSphereLayerPairingTriangleIso, isoTriangleOfIso₁₂_hom_hom₁]

@[simp] theorem adamsSphereLayerPairingTriangleIso_hom₂ (s t : ℕ) :
    (adamsSphereLayerPairingTriangleIso unit s t).hom.hom₂ =
      (adamsTowerSpherePairingIso unit s t).hom := by
  simp only [adamsSphereLayerPairingTriangleIso, isoTriangleOfIso₁₂_hom_hom₂]

/-- The actual tower-to-layer maps commute with the chosen layer-stage
pairing and the previously constructed tower pairing. -/
theorem adamsSphereLayerPairingIso_ι (s t : ℕ) :
    ((adamsLayerTriangle unit (𝟙_ C) s).mor₂ ▷ adamsTower unit (𝟙_ C) t) ≫
        (adamsSphereLayerPairingIso unit s t).hom =
      (adamsTowerSpherePairingIso unit s t).hom ≫
        (adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
  have h := (adamsSphereLayerPairingTriangleIso unit s t).hom.comm₂
  rw [adamsSphereLayerPairingTriangleIso_hom₂] at h
  exact h

/-- The first-input boundary formula retains the actual connecting maps
and the tensor functor's suspension comparison. It is not the two-term
Leibniz formula for a product of two layer classes. -/
theorem adamsSphereLayerPairingIso_δ (s t : ℕ) :
    (adamsSphereLayerPairingIso unit s t).hom ≫
        (adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      ((adamsLayerTriangle unit (𝟙_ C) s).mor₃ ▷ adamsTower unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t))
          (1 : ℤ)).hom.app (adamsTower unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso unit (s + 1) t).hom⟦(1 : ℤ)⟧' := by
  have h := (adamsSphereLayerPairingTriangleIso unit s t).hom.comm₃
  rw [adamsSphereLayerPairingTriangleIso_hom₁] at h
  exact h.symm.trans (Category.assoc _ _ _)

end
end KIP126.Classical.Adams
