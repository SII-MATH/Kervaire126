import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Right.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]
  [∀ Y : C, (tensorLeft Y).CommShift ℤ]
  [∀ Y : C, (tensorLeft Y).IsTriangulated]

@[simp] theorem adamsSphereTowerLayerPairingTriangleIso_hom₁
    (h : UnitFiberInclusionCommutes unit) (s t : ℕ) :
    (adamsSphereTowerLayerPairingTriangleIso unit h s t).hom.hom₁ =
      adamsTowerSpherePairingNextRight unit s t := by
  simp only [adamsSphereTowerLayerPairingTriangleIso, isoTriangleOfIso₁₂_hom_hom₁,
    Iso.trans_hom, eqToIso.hom, adamsTowerSpherePairingNextRight]
  rfl

@[simp] theorem adamsSphereTowerLayerPairingTriangleIso_hom₂
    (h : UnitFiberInclusionCommutes unit) (s t : ℕ) :
    (adamsSphereTowerLayerPairingTriangleIso unit h s t).hom.hom₂ =
      (adamsTowerSpherePairingIso unit s t).hom := by
  simp only [adamsSphereTowerLayerPairingTriangleIso, isoTriangleOfIso₁₂_hom_hom₂]

/-- Compatibility with the actual second-input tower-to-layer map. -/
theorem adamsSphereTowerLayerPairingIso_ι (h : UnitFiberInclusionCommutes unit)
    (s t : ℕ) :
    (adamsTower unit (𝟙_ C) s ◁ (adamsLayerTriangle unit (𝟙_ C) t).mor₂) ≫
        (adamsSphereTowerLayerPairingIso unit h s t).hom =
      (adamsTowerSpherePairingIso unit s t).hom ≫
        (adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
  have hcomm := (adamsSphereTowerLayerPairingTriangleIso unit h s t).hom.comm₂
  rw [adamsSphereTowerLayerPairingTriangleIso_hom₂] at hcomm
  exact hcomm

/-- The second-input boundary formula, retaining the left tensor functor's
suspension comparison. These two separate one-sided formulas do not yet
give the coherent two-layer product needed for Leibniz. -/
theorem adamsSphereTowerLayerPairingIso_δ (h : UnitFiberInclusionCommutes unit)
    (s t : ℕ) :
    (adamsSphereTowerLayerPairingIso unit h s t).hom ≫
        (adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      (adamsTower unit (𝟙_ C) s ◁ (adamsLayerTriangle unit (𝟙_ C) t).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower unit (𝟙_ C) s))
          (1 : ℤ)).hom.app (adamsTower unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingNextRight unit s t)⟦(1 : ℤ)⟧' := by
  have hcomm := (adamsSphereTowerLayerPairingTriangleIso unit h s t).hom.comm₃
  rw [adamsSphereTowerLayerPairingTriangleIso_hom₁] at hcomm
  exact hcomm.symm.trans (Category.assoc _ _ _)

/-- The two chosen mixed pairings agree after the respective tower-to-layer
maps. This equality on the common tower-tower source does not assert a
coherent gluing or a product on two layers. -/
theorem adamsSphereMixedLayerPairings_agree (h : UnitFiberInclusionCommutes unit)
    (s t : ℕ) :
    ((adamsLayerTriangle unit (𝟙_ C) s).mor₂ ▷ adamsTower unit (𝟙_ C) t) ≫
        (adamsSphereLayerPairingIso unit s t).hom =
      (adamsTower unit (𝟙_ C) s ◁ (adamsLayerTriangle unit (𝟙_ C) t).mor₂) ≫
        (adamsSphereTowerLayerPairingIso unit h s t).hom :=
  (adamsSphereLayerPairingIso_ι unit s t).trans
    (adamsSphereTowerLayerPairingIso_ι unit h s t).symm

end
end KIP126.Classical.Adams
