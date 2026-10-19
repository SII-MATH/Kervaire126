module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Order.Lattice

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

/-- The least barycentric coordinate away from the omitted horn face. -/
noncomputable def hornMin {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (n+1) => x (i.succAbove j))

/-- Retraction coordinates: move the common minimum of the other
coordinates to the distinguished vertex. -/
noncomputable def hornRetractionCoordinates {n : ℕ} (i : Fin (n+2))
    (x : stdSimplex ℝ (Fin (n+2))) (j : Fin (n+2)) : ℝ :=
  if j = i then x i + (n+1 : ℕ) * hornMin i x else x j - hornMin i x

end KIP126.Topology.SimplicialRealization
