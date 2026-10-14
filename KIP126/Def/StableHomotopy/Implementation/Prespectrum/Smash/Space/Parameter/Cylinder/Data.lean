module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Iso.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

local instance : T2Space intervalBoundaryObject := inferInstanceAs (T2Space {t : I // t = 0 ∨ t = 1})

/-- The actual product with the interval yields the original reduced
cylinder of the parameter tensor. -/
noncomputable def spaceSmashParameterCylinderIso (T : TopCat.{0})
    [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (TopCat.of (I × T))) X ≅
      cylinderFunctor.obj (spaceSmash (BasedSpace.adjoinPoint T) X) :=
  (spaceSmashParameterProductIso (TopCat.of I) T X).symm ≪≫
    spaceSmashIntervalIso (spaceSmash (BasedSpace.adjoinPoint T) X)

/-- The actual product with the two interval endpoints yields the two
original copies of the parameter tensor. -/
noncomputable def spaceSmashParameterEndpointsIso (T : TopCat.{0})
    [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (TopCat.of (intervalBoundaryObject × T))) X ≅
      spaceSmash (BasedSpace.adjoinPoint T) X ⨿ spaceSmash (BasedSpace.adjoinPoint T) X :=
  (spaceSmashParameterProductIso intervalBoundaryObject T X).symm ≪≫
    spaceSmashIntervalBoundaryIso (spaceSmash (BasedSpace.adjoinPoint T) X)

end KIP126.StableHomotopy.Implementation.Prespectrum
