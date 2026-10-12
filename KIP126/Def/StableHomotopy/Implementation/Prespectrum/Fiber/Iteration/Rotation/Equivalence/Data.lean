module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual rotation comparison gives a specified source isomorphism
whose forward map retains the original loop-map projection exactly. -/
noncomputable def sourceFiberRotationIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.obj (Prespectrum.loop X) ≅
      sourceLocalization.obj (fiber (fiberConnecting f)) := by
  letI := (stableEquivalence_iff_source_isIso _).mp (fiberRotationComparison_stableEquivalence f)
  exact asIso (sourceLocalization.map (fiberRotationComparison f))

end KIP126.StableHomotopy.Implementation.Prespectrum
