import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Tower.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Differential.Second.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.Proofs

/-! The second differential of the existing computed square is an actual
tower obstruction. These formulas do not assume that the obstruction vanishes. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

local notation "H₀" => standardFoundation.hf2

variable [MonoidalPreadditive standardFoundation.Spectrum]
  (R : Mod2RingStructure H₀) (K : Mod2CooperationKunneth H₀ R)
  (B : Mod2ReducedMilnorBasis H₀ R)
  [(tensorLeft (H₀).HF2).CommShift ℤ] [(tensorLeft (H₀).HF2).IsTriangulated]
  [(mod2UnitNatTrans H₀).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H₀ R K)
  (hD : Mod2KunnethDiagonalCompatible H₀ R K)
  (hU : Mod2KunnethUnitCompatible H₀ R K)
  (hM : Mod2MilnorCoproductCompatible H₀ R K B)
  (a : Mod2Cooperations H₀ 64) (ha : cooperationMilnorPolynomial H₀ R B 64 a = h6Polynomial)
  (u : adamsCycleAmbient (H₀).unit SphereSpectrum 2 128)
  (hu : adamsNextCycleToPage (H₀).unit SphereSpectrum 1 le_rfl 2 128 u =
    (adamsPageOneHomologyEquiv (H₀).unit SphereSpectrum 2 128).symm
      (sphereH6DoubleTensorRepresentative H₀ R K a (sphereMilnorUnitCoefficient H₀ R)))

include hK hD hU hM ha hu

/-- Any lift of the actual connecting image to T₄ computes d₂ of the
fixed data class. The target quotient has bidegree `(4,129)`. -/
theorem computedH6Square_d_two_value_of_double_lift
    (y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum 4))
    (hy : adamsI (H₀).unit SphereSpectrum 125 3 4 (by decide) y =
      adamsK (H₀).unit SphereSpectrum 2 128 u.val) :
    (adamsTowerSSDataPageIso (H₀).unit SphereSpectrum 4 129 0).hom
      ((sphereAdamsData.d 2 (2, 128)).hom computedH6Square) =
        adamsJToPage (H₀).unit SphereSpectrum 2 (by decide) 4 129 y :=
  adamsTower_d_two_h6_value_of_lift (H₀).unit SphereSpectrum computedH6Square u
    (computedH6Square_of_double_representative R K B hK hD hU hM a ha u hu) y hy

/-- Every actual double representative supplies a T₄ lift computing the
existing internal differential of the data square. -/
theorem computedH6Square_d_two_double_value_exists :
    ∃ y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum 4),
      adamsI (H₀).unit SphereSpectrum 125 3 4 (by decide) y =
        adamsK (H₀).unit SphereSpectrum 2 128 u.val ∧
      (adamsTowerSSDataPageIso (H₀).unit SphereSpectrum 4 129 0).hom
        ((sphereAdamsData.d 2 (2, 128)).hom computedH6Square) =
          adamsJToPage (H₀).unit SphereSpectrum 2 (by decide) 4 129 y :=
  adamsTower_d_two_h6_value_exists (H₀).unit SphereSpectrum computedH6Square u
    (computedH6Square_of_double_representative R K B hK hD hU hM a ha u hu)

/-- The actual obstruction d₂ vanishes precisely when k(u) lifts to T₅.
This equivalence supplies no such lift by itself. -/
theorem computedH6Square_d_two_eq_zero_iff_double_lift :
    (sphereAdamsData.d 2 (2, 128)).hom computedH6Square = 0 ↔
      ∃ y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum 5),
        adamsI (H₀).unit SphereSpectrum 125 3 5 (by decide) y =
          adamsK (H₀).unit SphereSpectrum 2 128 u.val :=
  adamsTower_d_two_h6_eq_zero_iff_lift (H₀).unit SphereSpectrum computedH6Square u
    (computedH6Square_of_double_representative R K B hK hD hU hM a ha u hu)

/-- Leibniz compatibility for the actual d₂ supplies the next tower lift of
the specified double representative. The compatibility remains an explicit
unproved premise, not a new axiom or a permanence assertion. -/
theorem computedH6Square_double_lift_five_of_leibniz
    (hL : linE2Presentation.SecondDifferentialLeibniz) :
    ∃ y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum 5),
      adamsI (H₀).unit SphereSpectrum 125 3 5 (by decide) y =
        adamsK (H₀).unit SphereSpectrum 2 128 u.val :=
  (computedH6Square_d_two_eq_zero_iff_double_lift R K B hK hD hU hM a ha u hu).mp
    (computedH6Square_d_two_eq_zero_of_leibniz hL)

end
end KIP126.Classical.Adams
