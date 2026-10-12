module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp, reassoc] theorem sourceFiberRotationIso_projection {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    (sourceFiberRotationIso f).hom ≫ sourceLocalization.map (fiberProjection (fiberConnecting f)) =
      sourceLocalization.map (loopMap f) := by
  change sourceLocalization.map (fiberRotationComparison f) ≫ _ = _
  rw [← Functor.map_comp,fiberRotationComparison_projection]

end KIP126.StableHomotopy.Implementation.Prespectrum
