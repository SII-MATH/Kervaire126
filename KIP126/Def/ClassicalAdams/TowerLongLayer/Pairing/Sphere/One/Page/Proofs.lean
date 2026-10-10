import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.One.Page.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Page.Proofs

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

theorem adamsSpherePageOneProduct_long (s t : ℕ) (u v : ℤ)
    (a : HomotopyGroup (u - s) (adamsLongLayer H.unit (𝟙_ C) 1 le_rfl s))
    (b : HomotopyGroup (v - t) (adamsLongLayer H.unit (𝟙_ C) 1 le_rfl t)) :
    adamsSpherePageOneProduct H R s t u v
      (adamsLongLayerToPage H.unit (𝟙_ C) 1 le_rfl s u a)
      (adamsLongLayerToPage H.unit (𝟙_ C) 1 le_rfl t v b) =
        adamsLongLayerToPage H.unit (𝟙_ C) 1 le_rfl ((s : ℤ) + (t : ℤ)) (u + v)
          (homotopyTensorPairing (u - s) (v - t)
            ((u + v) - ((s : ℤ) + (t : ℤ))) (by omega)
            (adamsSphereLongLayerOneProduct H R s t) a b) :=
  (adamsSphereLongLayerOnePairing H R s t u v).onPage_long
    (adamsSphereLongLayerOnePairing_projection H R s t u v)
    (AdamsLongLayerPairing.boundaryCompatible_one _) a b

end
end KIP126.Classical.Adams
