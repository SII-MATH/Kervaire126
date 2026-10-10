import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} {M : SphereH6LongLayerMaps H}
  {R : Mod2RingStructure H}
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

theorem SphereH6LongLayerMaps.Compatible.square (h : M.Compatible R) :
    (M.squarePairing R).ProjectionCompatible :=
  adamsSphereLongLayerPairing_projection H R 2 (by decide) 1 1 64 64 _ h.square_projection

theorem SphereH6LongLayerMaps.Compatible.left (h : M.Compatible R) :
    (M.leftPairing R).ProjectionCompatible :=
  adamsSphereLongLayerPairing_projection H R 2 (by decide) 3 1 65 64 _ h.left_projection

theorem SphereH6LongLayerMaps.Compatible.right (h : M.Compatible R) :
    (M.rightPairing R).ProjectionCompatible :=
  adamsSphereLongLayerPairing_projection H R 2 (by decide) 1 3 64 65 _ h.right_projection

end
end KIP126.Classical.Adams
