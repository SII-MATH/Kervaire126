module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Carrier.Homotopy.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped Classical

universe u

/-- The realization of a constant order map is the constant map at the
specified actual target vertex. -/
theorem orderConstant_realization (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (q : Q) (x : |nerve P|) :
    SSet.toTop.map (nerveMap (OrderHom.const P q).monotone.functor) x = orderVertex Q q := by
  apply eq_orderVertex_of_zero_coordinates Q _ q
  intro r hr
  rw [orderComplexCoordinates_natural]
  apply simplex_map_apply_not_range
  rintro ⟨p,hp⟩
  exact hr hp.symm

end KIP126.Topology.SimplicialRealization
