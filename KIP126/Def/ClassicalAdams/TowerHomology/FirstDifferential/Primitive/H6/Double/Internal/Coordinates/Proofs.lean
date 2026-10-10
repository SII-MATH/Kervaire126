import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.H6.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The constructed internal class has an actual Z₂ lift whose first-page
coordinate is exactly the existing h₆-square cocycle. This uses derived
coordinates, not the fixed Milnor page-comparison axiom. -/
theorem sphereH6DoubleInternalE2_polynomial_representative
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    ∃ u : adamsCycles H.unit SphereSpectrum 2 (by omega) 2 128,
      sphereFirstPageMilnorEquiv H R K B 2 128
        (adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 2 128 u) = h6SquareCochain ∧
      (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).hom
        (sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R)) =
          (adamsCycleBoundaries H.unit SphereSpectrum 2 (by omega) 2 128).mkQ u := by
  obtain ⟨u, hu, he⟩ := sphereH6DoubleInternalE2_representative H R K B hK hD hU hM a ha
    (sphereMilnorUnitCoefficient H R)
  refine ⟨u, ?_, he⟩
  rw [hu]
  exact sphereFirstPageMilnorEquiv_h6_double H R K B a ha

end
end KIP126.Classical.Adams
