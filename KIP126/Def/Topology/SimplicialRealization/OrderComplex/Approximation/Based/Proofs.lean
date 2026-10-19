module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Homotopy.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Vertices

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- A map preserving specified vertices has a genuine simplicial
approximation that preserves their actual iterated vertices, through a
homotopy relative to that same specified point. -/
theorem exists_iteratedOrderSubdivision_simplicial_approximation_based (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : C(|nerve P|,|nerve Q|)) (p : P) (q : Q)
    (hf : f (orderVertex P p) = orderVertex Q q) :
    ∃ (n : ℕ) (φ : nerve (iteratedOrderSubdivision P (n+1)) ⟶ nerve Q),
      SSet.toTop.map φ (orderVertex _ (iteratedOrderSubdivisionVertex P (n+1) p)) =
        orderVertex Q q ∧
      ContinuousMap.HomotopicRel
        (f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
          (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩)
        (SSet.toTop.map φ).hom
        {orderVertex _ (iteratedOrderSubdivisionVertex P (n+1) p)} := by
  obtain ⟨n,φ,H,_,hfix⟩ := exists_iteratedOrderSubdivision_simplicial_approximation P Q f
  have hb : f (iteratedOrderSubdivisionHomeomorph P (n+1)
      (orderVertex _ (iteratedOrderSubdivisionVertex P (n+1) p))) = orderVertex Q q := by
    rw [iteratedOrderSubdivisionHomeomorph_vertex]
    exact hf
  refine ⟨n,φ,?_,⟨⟨H,?_⟩⟩⟩
  · exact (H.apply_one _).symm.trans (hfix 1 _ q hb)
  · intro t x hx
    rcases hx with rfl
    exact (hfix t _ q hb).trans hb.symm

end KIP126.Topology.SimplicialRealization
