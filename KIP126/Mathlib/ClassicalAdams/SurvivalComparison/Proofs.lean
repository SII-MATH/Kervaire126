import KIP126.Mathlib.ClassicalAdams.StandardPage.Data
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Permanence.Proofs

namespace KIP126.Classical.Adams

open KIP126.Core.SpectralSequence

/-- Common-Z∞ nonzero survival and compatible nonzero finite-page survival
agree for every E₂ class of the fixed sphere tower. This is a comparison of
predicates, not an assertion that any specified class survives. -/
theorem survival_comparison (p : ℤ × ℤ) (x : sphereAdamsData.Page 2 p) :
    NonzeroSurvival sphereAdamsData p x ↔
      IsPermanent sphereAdams 2 (by decide) p (toStandardE2 p x) := by
  exact adamsTower_survival_comparison standardFoundation.hf2.unit
    KIP126.StableHomotopy.SphereSpectrum p x

end KIP126.Classical.Adams
