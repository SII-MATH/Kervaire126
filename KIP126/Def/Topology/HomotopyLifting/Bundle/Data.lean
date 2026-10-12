module

public import KIP126.Def.Topology.Cube.Grid.Layers.Data
public import KIP126.Def.Topology.HomotopyLifting.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval

/-- The standard cylinder bottom and side are the global grid horn after
inserting the time parameter as the first cube coordinate. -/
def gridHornHomeomorph (n : ℕ) :
    CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)) ≃ₜ
      Cube.gridGlobalHorn n :=
  (cubeCylinderHomeomorph n).subtype (fun _ => Iff.rfl)

end KIP126.Topology.HomotopyLifting
