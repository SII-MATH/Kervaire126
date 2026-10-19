module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data
public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The specified strict mapping-path projection has actual full
boundary lifting whenever the original map is levelwise weakly equivalent
at every point; its zero-dimensional lift uses the actual basepoint. -/
theorem mappingPathProjection_level_hasCubeBoundaryLifting
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n (x : X.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r))
    (n : ℕ) :
    KIP126.Topology.HomotopyLifting.HasCubeBoundaryLifting ((mappingPathProjection f).level n) :=
  KIP126.Topology.HomotopyLifting.mappingPathEndpoint_hasCubeBoundaryLifting
    (f.level n) (X.level n).point (hf n)

end KIP126.StableHomotopy.Implementation.Prespectrum
