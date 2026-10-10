import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Data

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
  (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
  (x : Mod2Homology H 0 SphereSpectrum)

/-- The constructed internal class has an actual Z₂ representative of the
twice-applied tensor boundary, not merely a class of the right degree. -/
theorem sphereH6DoubleInternalE2_representative :
    ∃ u : adamsCycles H.unit SphereSpectrum 2 (by omega) 2 128,
      adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 2 128 u =
        (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
          (sphereH6DoubleTensorRepresentative H R K a x) ∧
      (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).hom
        (sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x) =
          (adamsCycleBoundaries H.unit SphereSpectrum 2 (by omega) 2 128).mkQ u := by
  obtain ⟨u, hu⟩ := adamsNextCycle_exists_of_differential_eq_zero H.unit SphereSpectrum
    1 le_rfl 2 128 _ (sphereAdamsDifferential_one_h6_double_zero H R K B hK hD hU hM a ha x)
  exact ⟨u, hu, adamsTowerE2OfFirstCycle_comparison H.unit SphereSpectrum 2 128 _ _ u hu⟩

/-- The remaining E₂ nonvanishing question is an actual B₂ question.
This equivalence does not assume or prove the required non-membership. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff
    (u : adamsCycles H.unit SphereSpectrum 2 (by omega) 2 128)
    (hu : adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 2 128 u =
      (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H R K a x)) :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x = 0 ↔
      u.val ∈ adamsBoundaries H.unit SphereSpectrum 2 (by omega) 2 128 :=
  adamsTowerE2OfFirstCycle_eq_zero_iff H.unit SphereSpectrum 2 128 _ _ u hu

end
end KIP126.Classical.Adams
