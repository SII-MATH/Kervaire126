import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Polynomial.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Boundary.Proofs

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
  (hK : Mod2KunnethSuspensionCompatible H R K)
  (hD : Mod2KunnethDiagonalCompatible H R K)
  (hU : Mod2KunnethUnitCompatible H R K)
  (hM : Mod2MilnorCoproductCompatible H R K B)

include hK hD hU hM

/-- The actual internal double class with normalized sphere coefficient is
nonzero on E₂. The cobar non-boundary input is now proved, not assumed.
Fixed Lin identification and higher-page survival are separate obligations. -/
theorem sphereH6DoubleInternalE2_ne_zero (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R) ≠ 0 :=
  (sphereH6DoubleInternalE2_ne_zero_iff_cobar_nonboundary H R K B hK hD hU hM a ha).mpr
    h6SquareCochain_not_boundary

/-- Below-page structure and coherence suffice to construct a nonzero
class in the actual sphere tower's internal E₂ page at (2,128). -/
theorem sphereAdamsInternalE2_h6_double_nonzero_exists :
    ∃ x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (2, 128), x ≠ 0 := by
  obtain ⟨a, ha, _⟩ := cooperationMilnorPolynomial_h6_existsUnique H R B
  exact ⟨sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R),
    sphereH6DoubleInternalE2_ne_zero H R K B hK hD hU hM a ha⟩

end
end KIP126.Classical.Adams
