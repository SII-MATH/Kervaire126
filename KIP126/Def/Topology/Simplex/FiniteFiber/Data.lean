module

public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs

@[expose] public section

namespace KIP126.Topology.Simplex

/-- The finite set of vertices having positive weight in an actual
barycentric point. -/
noncomputable def positiveSupport {A : Type*} [Fintype A] (x : stdSimplex ℝ A) : Finset A :=
  Finset.univ.filter (fun a => 0 < x a)

end KIP126.Topology.Simplex
