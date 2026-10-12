module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Operation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- A continuous based family commuting with the actual bonds defines a
strict map to the path prespectrum. -/
def loopGroupPathMap {A X : Prespectrum.{u}}
    (H : ∀ n, C(A.level n × I, (Prespectrum.loop X).level n))
    (hp : ∀ n s, H n ((A.level n).point,s) = ((Prespectrum.loop X).level n).point)
    (hb : ∀ n x t s, H (n+1) (A.bond n (x,t),s) = loopBond X n (H n (x,s),t)) :
    A ⟶ pathPrespectrum (Prespectrum.loop X) where
  level n := (H n).curry
  point n := by apply ContinuousMap.ext; intro s; exact hp n s
  bond n x t := by apply ContinuousMap.ext; intro s; exact hb n x t s

end KIP126.StableHomotopy.Implementation.Prespectrum
