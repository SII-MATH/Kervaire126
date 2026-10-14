module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Equivalence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Lift the actual retained path of every fiber point by the already
constructed strict mapping-path lifting formula. -/
noncomputable def mappingPathFiberLift {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (mappingPathProjection f) ⟶ pathPrespectrum (mappingPath f) :=
  mappingPathLift f (fiberProjection (mappingPathProjection f))
    (fiberNullPath (mappingPathProjection f)) (fiberNullPath_zero (mappingPathProjection f)).symm

/-- The actual lifted endpoint retracts onto the strict kernel of the
mapping-path projection, with no unproved lifting premise. -/
noncomputable def mappingPathStrictFiberRetraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (mappingPathProjection f) ⟶ strictFiber (mappingPathProjection f) :=
  strictFiberRetraction (mappingPathProjection f) (mappingPathFiberLift f)
    (fun s => mappingPathLift_projection f _ _ _ s)

/-- The actual strict and path fibers of the mapping-path projection are
isomorphic in the specified ordinary stable localization. -/
noncomputable def sourceMappingPathStrictFiberIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.obj (strictFiber (mappingPathProjection f)) ≅
      sourceLocalization.obj (fiber (mappingPathProjection f)) :=
  sourceStrictFiberIso (mappingPathProjection f) (mappingPathFiberLift f)
    (fun s => mappingPathLift_projection f _ _ _ s) (mappingPathLift_zero f _ _ _)

end KIP126.StableHomotopy.Implementation.Prespectrum
