import KIP126.Def.ClassicalAdams.TowerLongLayer.One.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- A constructed one-step long-layer product, transported through the
specified projection isomorphisms from the actual coefficient product. -/
def adamsSphereLongLayerOneProduct (s t : ℕ) :
    adamsLongLayer H.unit (𝟙_ C) 1 le_rfl s ⊗
      adamsLongLayer H.unit (𝟙_ C) 1 le_rfl t ⟶
        adamsLongLayer H.unit (𝟙_ C) 1 le_rfl ((s : ℤ) + (t : ℤ)) :=
  (adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl s ⊗ₘ
    adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl t) ≫
      adamsSphereLayerProductOrdered H R s t ≫
        inv (adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl ((s : ℤ) + (t : ℤ)))

/-- The actual one-step representative pairing, with no free long-layer map. -/
def adamsSphereLongLayerOnePairing (s t : ℕ) (u v : ℤ) :
    AdamsLongLayerPairing H.unit (𝟙_ C) 1 le_rfl ((s : ℤ), u) ((t : ℤ), v) :=
  adamsSphereLongLayerPairing H R 1 le_rfl s t u v (adamsSphereLongLayerOneProduct H R s t)

end
end KIP126.Classical.Adams
