import KIP126.Def.StableHomotopy.Implementation.Fixed
import KIP126.Def.StageInput.Foundation
import KIP126.Def.ClassicalAdams.Convergence.BHS.Predicates
import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

/-! Applicability of BHS to the standard sphere in Def's fixed implementation.
The statement is independent of the selected route, literature package, and
program data. Its construction proof remains an explicit obligation. -/
namespace KIP126.Def

theorem standardSphereApplicability : Classical.Adams.BHSObjectApplicability
    fixedImplementation.foundationInput.countableProducts
    fixedImplementation.foundationInput.hf2.unit
    (StableHomotopy.SphereSpectrum
      (C := fixedImplementation.foundationInput.Spectrum)) := by
  sorry

/-- Separation of the Adams filtration on the fixed 2-completed sphere.
The applicability theorem above identifies the fixed object, while the
convergence-to-separation argument remains a visible proof obligation. -/
theorem standardSphereSeparated : Classical.Adams.ClassicalSphereSeparated
    Classical.Adams.standardFoundation.hf2 := by
  have h := standardSphereApplicability
  sorry

end KIP126.Def
