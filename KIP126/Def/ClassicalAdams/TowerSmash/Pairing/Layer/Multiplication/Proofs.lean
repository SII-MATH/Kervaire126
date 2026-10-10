import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Data
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Proofs

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

/-- The newly defined layer product is exactly coefficient multiplication
combined with the existing tower pairing under the existing layer comparisons. -/
theorem adamsSphereLayerProduct_comparison (s t : ℕ) :
    adamsSphereLayerProduct H R s t ≫ (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom =
      ((adamsLayerIso H.unit (𝟙_ C) s).hom ⊗ₘ
        (adamsLayerIso H.unit (𝟙_ C) t).hom) ≫
        mod2CoefficientPairing H R (adamsTowerSpherePairingIso H.unit s t).hom := by
  simp only [adamsSphereLayerProduct, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On two tower-to-layer images the coefficient-induced product agrees
with the actual tower pairing followed by the actual target layer projection. -/
theorem adamsSphereLayerProduct_ι (s t : ℕ) :
    ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ
        (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫
        adamsSphereLayerProduct H R s t =
      (adamsTowerSpherePairingIso H.unit s t).hom ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
  have hι (k : ℕ) : (adamsLayerTriangle H.unit (𝟙_ C) k).mor₂ ≫
      (adamsLayerIso H.unit (𝟙_ C) k).hom =
      adamsUnit H.unit (adamsTower H.unit (𝟙_ C) k) :=
    adamsLayerIso_ι H.unit (𝟙_ C) k
  apply (cancel_mono (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom).mp
  erw [Category.assoc, adamsSphereLayerProduct_comparison, ← Category.assoc,
    tensorHom_comp_tensorHom, hι, hι, mod2CoefficientPairing_unit]
  change (adamsTowerSpherePairingIso H.unit s t).hom ≫
      adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)) =
    ((adamsTowerSpherePairingIso H.unit s t).hom ≫
      (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂) ≫
      (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom
  exact (congrArg (fun f => (adamsTowerSpherePairingIso H.unit s t).hom ≫ f)
    (hι (t + s))).symm.trans (Category.assoc _ _ _).symm

end
end KIP126.Classical.Adams
