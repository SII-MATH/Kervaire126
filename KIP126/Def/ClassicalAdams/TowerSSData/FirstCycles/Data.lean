import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Proofs

/-! Send actual first-page cycles to the existing internal second page.
This uses the proved tower representative lift, not a coordinate input. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The internal E₂ class of an actual first-page cycle. Independence from
the chosen lift and its exact vanishing criterion are proved separately. -/
def adamsTowerE2OfFirstCycle (s t : ℤ)
    (z : adamsPage unit X 1 le_rfl s t)
    (hz : adamsDifferential unit X 1 le_rfl s t z = 0) :
    (adamsTowerInternalSpectralSequence unit X).Page 2 (s, t) :=
  (adamsTowerSSDataPageIso unit X s t 0).inv
    ((adamsCycleBoundaries unit X 2 (by omega) s t).mkQ
      (adamsNextCycle_exists_of_differential_eq_zero unit X 1 le_rfl s t z hz).choose)

end
end KIP126.Classical.Adams
