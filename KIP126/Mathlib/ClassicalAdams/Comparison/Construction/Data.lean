import KIP126.Mathlib.ClassicalAdams.Comparison.Data
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Page.Proofs
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Passage.Proofs

namespace KIP126.Classical.Adams

set_option backward.isDefEq.respectTransparency false

/-- The fixed sphere comparison, constructed from actual quotient
representatives, their differential, and the tower homology passage.
It does not depend on the Lin table, Milnor coordinates, or a survival claim. -/
noncomputable def sphereAdams_towerComparison : SphereTowerComparison where
  pageIso := adamsTowerPageComparison standardFoundation.hf2.unit
    KIP126.StableHomotopy.SphereSpectrum
  differential r hr p := by
    have h := adamsTowerPageComparison_differential standardFoundation.hf2.unit
      KIP126.StableHomotopy.SphereSpectrum r hr p
    simpa only [sphereAdamsData, sphereAdamsModel, adamsTowerInternalSpectralSequence,
      sphereAdams, mod2SphereAdams, adamsTowerPreSS] using h
  passage r hr p x y hx := adamsTowerPageComparison_passage standardFoundation.hf2.unit
    KIP126.StableHomotopy.SphereSpectrum r hr p x y hx

end KIP126.Classical.Adams
