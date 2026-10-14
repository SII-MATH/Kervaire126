module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Endpoint.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- The actual boundary of a relative cylinder: both target endpoints
and the full source cylinder, glued along both source endpoints. -/
noncomputable def cylinderBoundaryPushout {X Y : Prespectrum.{u}} (i : X ⟶ Y) :
    Prespectrum.{u} := pushout (coprod.map i i) (cylinderEndpoints X)

/-- The actual relative cylinder boundary includes in the original
target cylinder by the actual pushout universal map. -/
noncomputable def cylinderPushoutProduct {X Y : Prespectrum.{u}} (i : X ⟶ Y) :
    cylinderBoundaryPushout i ⟶ cylinderFunctor.obj Y :=
  pushout.desc (cylinderEndpoints Y) (cylinderFunctor.map i) (cylinderEndpoints_natural i)

end KIP126.StableHomotopy.Implementation.Prespectrum
