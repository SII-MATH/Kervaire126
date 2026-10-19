module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data
public import KIP126.Def.Topology.HomotopyLifting.Path.Loop.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u

/-- The actual strict loop functor preserves the actual full cubical
boundary lifting condition at every level. -/
theorem loopMap_level_hasCubeBoundaryLifting {E B : Prespectrum.{u}}
    (p : E ⟶ B) (hp : ∀ n, HasCubeBoundaryLifting (p.level n)) (n : ℕ) :
    HasCubeBoundaryLifting ((loopMap p).level n) :=
  (hp n).continuousBasedLoopMap (E.level n).point (B.level n).point (p.point n)

end KIP126.StableHomotopy.Implementation.Prespectrum
