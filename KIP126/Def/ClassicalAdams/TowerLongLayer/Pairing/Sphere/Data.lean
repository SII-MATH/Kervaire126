import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Homotopy.Data

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

/-- An actual long-layer spectrum map determines the candidate representative
pairing, whose first-page component is fixed to the coefficient product.
This construction neither chooses nor postulates that spectrum map. -/
def adamsSphereLongLayerPairing (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (μ : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        adamsLongLayer H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ))) :
    AdamsLongLayerPairing H.unit (𝟙_ C) r hr ((s : ℤ), u) ((t : ℤ), v) where
  first := adamsSphereE1Product H R s t u v
  long := homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
    (by omega) μ

end
end KIP126.Classical.Adams
