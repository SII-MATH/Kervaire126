import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
import KIP126.Def.ClassicalAdams.MilnorCooperations.Data

/-! Identify the differential used by the existing Milnor-coordinate interface
with the independently constructed coefficient-homology resolution formula.
No value of `MilnorCooperations` is required by this comparison. -/

namespace KIP126.Classical.Adams

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The exact differential appearing in `MilnorCooperations` is induced by
the unit-triangle boundary followed by the next unit. This does not establish
its further comparison with the Milnor coproduct differential. -/
theorem sphereFirstDifferential_homology
    (H : Mod2EilenbergMacLane (C := C)) (s t : ℕ)
    (x : adamsPage H.unit SphereSpectrum 1 (by decide) s t) :
    adamsPageOneHomologyEquiv H.unit SphereSpectrum (s + 1) t
      (sphereFirstDifferential H s t x) =
        adamsResolutionDifferential H.unit SphereSpectrum s t
          (adamsPageOneHomologyEquiv H.unit SphereSpectrum s t x) :=
  adamsPageD_one_homology H.unit SphereSpectrum s t x

end KIP126.Classical.Adams
