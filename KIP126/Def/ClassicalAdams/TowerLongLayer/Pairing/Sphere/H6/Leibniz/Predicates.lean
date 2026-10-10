import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Leibniz.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} (M : SphereH6LongLayerMaps H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The two-term long-layer boundary identity in the square's degrees, using
the actual adjacent-degree products, not arbitrary maps `L` and `R`.
The plus sign is the characteristic-two form after passage to the page;
this predicate does not assert a spectrum-level graded sign convention. -/
def SphereH6LongLayerMaps.RelativeBoundary (h : M.Compatible R) : Prop :=
  (M.squarePairing R).RelativeBoundaryFormula
    ((M.leftPairing R).onPage h.left h.left_boundary)
    ((M.rightPairing R).onPage h.right h.right_boundary) 1

end
end KIP126.Classical.Adams
