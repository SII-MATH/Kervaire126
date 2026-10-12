module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.NullPath
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual source loop lifts to the homotopy fiber of the connecting map,
retaining its explicit sliding nullhomotopy. -/
def fiberRotationComparison {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Prespectrum.loop X ⟶ fiber (fiberConnecting f) :=
  fiberLift (fiberConnecting f) (loopMap f) (fiberLoopNullPath f)
    (fiberLoopNullPath_zero f) (fiberLoopNullPath_one f)

/-- Compare the fiber of the connecting map with the second fiber of the
original projection, through the already constructed iteration comparison. -/
def fiberRotationTargetMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (fiberConnecting f) ⟶ fiber (fiberProjection (fiberProjection f)) :=
  fiberMap (fiberConnecting f) (fiberProjection (fiberProjection f))
    (fiberIterationComparison f) (𝟙 (fiber f))
    (by rw [Category.comp_id,fiberIterationComparison_projection])

end KIP126.StableHomotopy.Implementation.Prespectrum
