import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.One.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Page.Data

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

/-- The constructed coefficient product on the existing first quotient page.
Both descent conditions are proved, not supplied as additional inputs. -/
def adamsSpherePageOneProduct (s t : ℕ) (u v : ℤ) :
    adamsPage H.unit (𝟙_ C) 1 le_rfl s u →ₗ[ℤ]
      adamsPage H.unit (𝟙_ C) 1 le_rfl t v →ₗ[ℤ]
        adamsPage H.unit (𝟙_ C) 1 le_rfl ((s : ℤ) + (t : ℤ)) (u + v) :=
  (adamsSphereLongLayerOnePairing H R s t u v).onPage
    (adamsSphereLongLayerOnePairing_projection H R s t u v)
    (AdamsLongLayerPairing.boundaryCompatible_one _)

end
end KIP126.Classical.Adams
