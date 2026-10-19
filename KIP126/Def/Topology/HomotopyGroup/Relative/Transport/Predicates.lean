module

public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u

/-- An actual homotopy of cube maps with a prescribed, possibly
nonconstant, path of boundary maps. -/
def CubeBoundaryTransport {Y : Type u} [TopologicalSpace Y] {n : ℕ}
    {a b : C(↥(_root_.Cube.boundary (Fin n)),Y)} (γ : Path a b)
    (p q : C(Fin n → I,Y)) : Prop :=
  ∃ H : p.Homotopy q,
    ∀ t (x : ↥(_root_.Cube.boundary (Fin n))), H (t,x.val) = γ t x

end KIP126.Topology
