import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Lifting.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Construction.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : Mod2EilenbergMacLane (C := C)} (B : SphereH6BoundaryLifts H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The three required actual long-layer spectrum maps, now constructed
from lower connecting-map lifts with their connecting maps retained. -/
def SphereH6BoundaryLifts.toLongLayerMaps (h : B.FitsProducts R) : SphereH6LongLayerMaps H where
  square := adamsSphereLongLayerProductOfBoundaryLift H R 2 (by decide) 1 1 B.square h.square
  left := adamsSphereLongLayerProductOfBoundaryLift H R 2 (by decide) 3 1 B.left h.left
  right := adamsSphereLongLayerProductOfBoundaryLift H R 2 (by decide) 1 3 B.right h.right

end
end KIP126.Classical.Adams
