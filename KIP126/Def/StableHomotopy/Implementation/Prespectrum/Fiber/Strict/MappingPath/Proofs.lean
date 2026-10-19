module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.MappingPath.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem mappingPathFiberLift_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathFiberLift f ≫ pathEvaluation (mappingPath f) 0 = fiberProjection (mappingPathProjection f) :=
  mappingPathLift_zero f _ _ _

@[simp] theorem mappingPathFiberLift_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) (s : unitInterval) :
    mappingPathFiberLift f ≫ pathEvaluation (mappingPath f) s ≫ mappingPathProjection f =
      fiberNullPath (mappingPathProjection f) ≫ pathEvaluation Y s :=
  mappingPathLift_projection f _ _ _ s

/-- Unconditional comparison for the actual mapping-path projection. Its
required universal lift has been constructed explicitly, including strict bonds. -/
theorem mappingPathStrictFiberInclusion_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (strictFiberInclusion (mappingPathProjection f)) :=
  strictFiberInclusion_stableEquivalence (mappingPathProjection f) (mappingPathFiberLift f)
    (mappingPathFiberLift_projection f) (mappingPathFiberLift_zero f)

/-- The actual endpoint retraction is also an unconditional stable equivalence. -/
theorem mappingPathStrictFiberRetraction_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (mappingPathStrictFiberRetraction f) :=
  strictFiberRetraction_stableEquivalence (mappingPathProjection f) (mappingPathFiberLift f)
    (mappingPathFiberLift_projection f) (mappingPathFiberLift_zero f)

end KIP126.StableHomotopy.Implementation.Prespectrum
