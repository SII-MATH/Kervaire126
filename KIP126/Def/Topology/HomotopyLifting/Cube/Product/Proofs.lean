module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Product.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u

instance cubeObject_compactSpace (n : ℕ) : CompactSpace (cubeObject.{u} n) :=
  inferInstanceAs (CompactSpace (ULift.{u} (Fin n → I)))

instance cubeObject_t2Space (n : ℕ) : T2Space (cubeObject.{u} n) :=
  inferInstanceAs (T2Space (ULift.{u} (Fin n → I)))

end KIP126.Topology.HomotopyLifting
