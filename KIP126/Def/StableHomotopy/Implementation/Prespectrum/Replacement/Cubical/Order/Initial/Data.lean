module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization
open KIP126.Topology.HomotopyLifting

universe u

/-- The actual initial one-point level is homeomorphic to an actual finite
order realization, using the zero-dimensional cube-cone comparison. -/
noncomputable def zeroPrespectrumLevelOrderHomeomorph (n : ℕ) :
    |nerve (WithTop (orderProperChains (ULift.{u} (Fin 1))))| ≃ₜ
      (zeroPrespectrum.{u}.level n) := by
  letI : Unique (cubeObject.{u} 0) :=
    inferInstanceAs (Unique (ULift.{u} (Fin 0 → unitInterval)))
  letI : Unique (zeroPrespectrum.{u}.level n) := inferInstanceAs (Unique PUnit)
  exact (orderBoundaryConeCubeHomeomorph.{u} 0).trans (Homeomorph.homeomorphOfUnique _ _)

end KIP126.StableHomotopy.Implementation.Prespectrum
