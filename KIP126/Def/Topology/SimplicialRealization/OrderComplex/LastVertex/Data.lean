module

public import Mathlib.Order.NonemptyFiniteChains
public import Mathlib.Order.Preorder.Finite

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

/-- The greatest vertex of a nonempty finite chain in a partial order. -/
noncomputable def orderChainMaximum {P : Type*} [PartialOrder P]
    (c : PartialOrder.NonemptyFiniteChains P) : P :=
  Classical.choose (c.finset.exists_maximal c.nonempty)

end KIP126.Topology.SimplicialRealization
