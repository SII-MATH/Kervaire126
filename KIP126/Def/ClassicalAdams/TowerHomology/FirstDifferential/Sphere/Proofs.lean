import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Sphere.Proofs

/-! The actual initial sphere boundary and first differential vanish.
No ring, Künneth, Milnor, or extra tensor exactness witness is needed. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- Every initial coefficient class comes from the unit, so exactness
kills its actual resolution boundary. -/
theorem sphereAdamsResolutionBoundary_zero (n : ℤ)
    (x : Mod2Homology H n SphereSpectrum) :
    adamsResolutionBoundary H.unit SphereSpectrum 0 n x = 0 := by
  rw [← adamsResolutionSequence_connecting]
  exact (les_homotopy_exact_g (adamsResolutionSequence H SphereSpectrum) n x).mpr
    (mod2SphereHomology_unit_surjective H n x)

/-- The actual representative first differential out of the initial
sphere stage is zero, independently of all coordinate inputs. -/
theorem sphereAdamsHomologyD1_zero (n : ℤ) (x : Mod2Homology H n SphereSpectrum) :
    adamsHomologyD1 H SphereSpectrum n x = 0 := by
  change inducedMap (adamsUnit H.unit (fiber (adamsUnit H.unit SphereSpectrum))) (n - 1)
    (adamsResolutionBoundary H.unit SphereSpectrum 0 n x) = 0
  rw [sphereAdamsResolutionBoundary_zero]
  exact (inducedMap (adamsUnit H.unit (fiber (adamsUnit H.unit SphereSpectrum)))
    (n - 1)).map_zero

/-- The actual quotient-page differential out of filtration zero is zero.
This includes internal degree zero, not just the vanishing coefficient groups. -/
theorem sphereAdamsPageD_one_filtration_zero (t : ℤ)
    (x : adamsPage H.unit SphereSpectrum 1 le_rfl 0 t) :
    (adamsPageD H.unit SphereSpectrum 1 le_rfl (0, t) (1, t)).hom x = 0 := by
  apply (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 t).injective
  have h := adamsPageD_one_homologyD1 H SphereSpectrum 0 t x
  erw [sphereAdamsHomologyD1_zero, map_zero] at h
  exact h.trans (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 t).map_zero.symm

end

end KIP126.Classical.Adams
