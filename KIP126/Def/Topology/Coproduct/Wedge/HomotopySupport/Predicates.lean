module

public import KIP126.Def.Topology.Coproduct.Wedge.Subfamily.Data

@[expose] public section

namespace KIP126.Topology

/-- The points contained in every open neighborhood of the specified
basepoint. No separation axiom is imposed. -/
def basepointNeighborhoodKernel {X : Type*} [TopologicalSpace X] (x₀ : X) : Set X :=
  {x | ∀ U : Set X, IsOpen U → x₀ ∈ U → x ∈ U}

end KIP126.Topology
