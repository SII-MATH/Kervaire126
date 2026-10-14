module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Data
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

/-- The original stable class represented by a based self-map of an
original sphere level and the original canonical cube. This does not
assume any degree classification of sphere maps. -/
def sphereSelfMapClass (n : ℕ) (f : sphereLevel n ⟶ sphereLevel n) :
    StableHomotopy sphere 0 :=
  loopClass sphere 0 n n (by omega)
    (KIP126.Topology.continuousGenLoopMap f.map
      (sphereLevel n).point (sphereLevel n).point f.point n (sphereCube n))

end KIP126.StableHomotopy.Implementation.Prespectrum
