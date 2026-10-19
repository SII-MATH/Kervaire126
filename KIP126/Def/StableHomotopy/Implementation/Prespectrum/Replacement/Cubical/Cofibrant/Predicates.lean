module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Lifting.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u

/-- Actual left lifting against every strict map with full cube-boundary
lifting on each of its original topological levels. -/
def IsCubicallyCofibrant (X : Prespectrum.{u}) : Prop :=
  ∀ {E B : Prespectrum.{u}} (p : E ⟶ B),
    (∀ n,HasCubeBoundaryLifting (p.level n)) →
      HasLiftingProperty (zeroMap zeroPrespectrum X) p

end KIP126.StableHomotopy.Implementation.Prespectrum
