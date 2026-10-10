import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Restrictions.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- In the existing coefficient coordinates, restricting the right input
of the actual layer product to the tower image removes the coefficient
multiplication. No comparison with a chosen mixed completion is assumed. -/
theorem adamsSphereLayerProduct_ι_right_comparison (s t : ℕ) :
    (((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom =
      (α_ H.HF2 (adamsTower H.unit (𝟙_ C) s) (adamsTower H.unit (𝟙_ C) t)).hom ≫
        H.HF2 ◁ (adamsTowerSpherePairingIso H.unit s t).hom := by
  have hι : (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂ ≫
      (adamsLayerIso H.unit (𝟙_ C) t).hom =
      adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t) := adamsLayerIso_ι H.unit (𝟙_ C) t
  have htensor :
      ((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
          (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫
          ((adamsLayerIso H.unit (𝟙_ C) s).hom ⊗ₘ (adamsLayerIso H.unit (𝟙_ C) t).hom) =
        𝟙 (H.HF2 ⊗ adamsTower H.unit (𝟙_ C) s) ⊗ₘ
          adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t) :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (Iso.inv_hom_id _) hι)
  erw [Category.assoc, adamsSphereLayerProduct_comparison, ← Category.assoc, htensor]
  rw [id_tensorHom]
  exact mod2CoefficientPairing_unit_right H R _

/-- The left-input restriction retains the braiding that moves the other
coefficient factor past the first tower stage. Again the formula is for
the actual layer product, not for a separately chosen triangle completion. -/
theorem adamsSphereLayerProduct_ι_left_comparison (s t : ℕ) :
    (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ
        (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom =
      (α_ (adamsTower H.unit (𝟙_ C) s) H.HF2 (adamsTower H.unit (𝟙_ C) t)).inv ≫
        ((β_ (adamsTower H.unit (𝟙_ C) s) H.HF2).hom ▷ adamsTower H.unit (𝟙_ C) t) ≫
        (α_ H.HF2 (adamsTower H.unit (𝟙_ C) s) (adamsTower H.unit (𝟙_ C) t)).hom ≫
        H.HF2 ◁ (adamsTowerSpherePairingIso H.unit s t).hom := by
  have hι : (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ≫
      (adamsLayerIso H.unit (𝟙_ C) s).hom =
      adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s) := adamsLayerIso_ι H.unit (𝟙_ C) s
  have htensor :
      ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫
          ((adamsLayerIso H.unit (𝟙_ C) s).hom ⊗ₘ (adamsLayerIso H.unit (𝟙_ C) t).hom) =
        adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s) ⊗ₘ
          𝟙 (H.HF2 ⊗ adamsTower H.unit (𝟙_ C) t) :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) hι (Iso.inv_hom_id _))
  erw [Category.assoc, adamsSphereLayerProduct_comparison, ← Category.assoc, htensor]
  rw [tensorHom_id]
  exact mod2CoefficientPairing_unit_left H R _

end
end KIP126.Classical.Adams
