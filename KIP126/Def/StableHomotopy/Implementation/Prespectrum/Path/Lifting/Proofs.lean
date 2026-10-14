module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Data
public import KIP126.Def.Topology.HomotopyLifting.Path.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology.HomotopyLifting

universe u

/-- The actual strict path functor preserves every level's genuine
full cubical boundary lifting property. -/
theorem pathMap_level_hasCubeBoundaryLifting {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : ∀ n, HasCubeBoundaryLifting (f.level n)) (n : ℕ) :
    HasCubeBoundaryLifting ((pathMap f).level n) :=
  (hf n).pathPostcomp

end KIP126.StableHomotopy.Implementation.Prespectrum
