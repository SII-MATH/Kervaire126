module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data
public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The specified actual prespectrum mapping-path projection has full
cubical homotopy lifting at every level, preserving arbitrary prescribed
boundary lifts, including their retained paths. -/
theorem mappingPathProjection_level_hasCubicalLifting
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    KIP126.Topology.HomotopyLifting.HasCubicalLifting ((mappingPathProjection f).level n) :=
  KIP126.Topology.HomotopyLifting.mappingPathEndpoint_hasCubicalLifting (f.level n)

end KIP126.StableHomotopy.Implementation.Prespectrum
