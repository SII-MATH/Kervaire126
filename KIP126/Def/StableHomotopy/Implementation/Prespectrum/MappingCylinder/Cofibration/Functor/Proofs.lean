module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Adjunction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Lifting.Proofs
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The original cylinder functor preserves actual cubical
cofibrations, by the constructed strict adjunction and actual full
boundary lifting on the original compact-open path spaces. -/
theorem IsCubicalCofibration.cylinder {X Y : Prespectrum.{u}}
    {i : X ⟶ Y} (hi : IsCubicalCofibration i) :
    IsCubicalCofibration (cylinderFunctor.map i) := by
  intro E B p hp
  apply (cylinderPathAdjunction.hasLiftingProperty_iff i p).mpr
  exact hi (pathMap p) (pathMap_level_hasCubeBoundaryLifting p hp)

end KIP126.StableHomotopy.Implementation.Prespectrum
