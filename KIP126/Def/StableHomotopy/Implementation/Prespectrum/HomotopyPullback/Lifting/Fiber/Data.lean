module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Lifting
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.MappingPath.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Pullback
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Fiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Lift the actual retained null-path of a point in the fiber of the
homotopy-pullback projection. -/
noncomputable def homotopyPullbackFiberLift {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    fiber (homotopyPullbackSnd f g) ⟶ pathPrespectrum (homotopyPullback f g) :=
  homotopyPullbackLiftHomotopy f g (fiberProjection (homotopyPullbackSnd f g))
    (fiberNullPath (homotopyPullbackSnd f g)) (fiberNullPath_zero (homotopyPullbackSnd f g)).symm

/-- The strict kernel and actual homotopy fiber of the pullback projection
are equivalent, using the constructed lift with no added lifting premise. -/
noncomputable def sourceHomotopyPullbackStrictFiberIso {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    sourceLocalization.obj (strictFiber (homotopyPullbackSnd f g)) ≅
      sourceLocalization.obj (fiber (homotopyPullbackSnd f g)) :=
  sourceStrictFiberIso (homotopyPullbackSnd f g) (homotopyPullbackFiberLift f g)
    (fun s => homotopyPullbackLiftHomotopy_projection f g
      (fiberProjection (homotopyPullbackSnd f g)) (fiberNullPath (homotopyPullbackSnd f g))
      (fiberNullPath_zero (homotopyPullbackSnd f g)).symm s)
    (homotopyPullbackLiftHomotopy_zero f g
      (fiberProjection (homotopyPullbackSnd f g)) (fiberNullPath (homotopyPullbackSnd f g))
      (fiberNullPath_zero (homotopyPullbackSnd f g)).symm)

/-- Pulling back the mapping-path projection preserves its homotopy fiber,
through the explicit strict-kernel comparison. -/
noncomputable def sourceHomotopyPullbackFiberIso {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    sourceLocalization.obj (fiber (homotopyPullbackSnd f g)) ≅
      sourceLocalization.obj (fiber f) :=
  (sourceHomotopyPullbackStrictFiberIso f g).symm ≪≫
    sourceLocalization.mapIso (strictFiberPullbackIso (mappingPathProjection f) g) ≪≫
    sourceLocalization.mapIso (fiberHomotopyPullbackIso f).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
