module

public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u

/-- A cubical homotopy transporting its entire boundary along one
specified path of basepoints. -/
def GenLoopTransport {Y : Type u} [TopologicalSpace Y] {a b : Y}
    (γ : Path a b) {n : ℕ} (p : GenLoop (Fin n) Y a) (q : GenLoop (Fin n) Y b) : Prop :=
  ∃ H : p.val.Homotopy q.val,
    ∀ t x, x ∈ _root_.Cube.boundary (Fin n) → H (t,x) = γ t

end KIP126.Topology
