module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Predicates

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u

/-- The actual left lifting property against every strict map with full
cubical boundary lifting at all levels. -/
def IsCubicalCofibration {X Y : Prespectrum.{u}} (i : X ⟶ Y) : Prop :=
  ∀ {E B : Prespectrum.{u}} (p : E ⟶ B),
    (∀ n, HasCubeBoundaryLifting (p.level n)) → HasLiftingProperty i p

end KIP126.StableHomotopy.Implementation.Prespectrum
