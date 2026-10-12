module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Vertices.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The geometric barycenter of a singleton chain is the original
simplex vertex. -/
theorem orderChainBarycenter_singleton (P : Type u) [PartialOrder P] [Fintype P]
    (p : P) : orderChainBarycenter P (orderSingletonChain p) = stdSimplex.vertex p := by
  apply stdSimplex.ext
  funext q
  simp [orderChainBarycenter_apply,orderSingletonChain,stdSimplex.vertex,Pi.single_apply,eq_comm]

/-- A subdivision vertex maps to the genuine barycenter of its chain. -/
theorem orderSubdivisionHomeomorph_vertex (P : Type u) [PartialOrder P] [Fintype P]
    (c : PartialOrder.NonemptyFiniteChains P) :
    orderComplexCoordinates P (orderSubdivisionHomeomorph P
      (orderVertex _ c)) = orderChainBarycenter P c := by
  rw [orderSubdivisionHomeomorph_coordinates,orderVertex,orderSubdivisionCoordinates_simplex]
  apply Subtype.ext
  exact Simplex.combinationCoordinates_vertex (fun _ : Fin 1 => orderChainBarycenter P c) 0

/-- A singleton subdivision vertex maps to the corresponding original
vertex under the actual homeomorphism. -/
theorem orderSubdivisionHomeomorph_singleton_vertex (P : Type u)
    [PartialOrder P] [Fintype P] (p : P) :
    orderSubdivisionHomeomorph P (orderVertex _ (orderSingletonChain p)) =
      orderVertex P p := by
  apply orderComplexCoordinates_injective P
  rw [orderSubdivisionHomeomorph_vertex,orderChainBarycenter_singleton,
    orderComplexCoordinates_vertex]

/-- Every iterated geometric homeomorphism sends the repeated singleton
vertex to its specified original vertex. -/
theorem iteratedOrderSubdivisionHomeomorph_vertex (P : Type u)
    [PartialOrder P] [Fintype P] (n : ℕ) (p : P) :
    iteratedOrderSubdivisionHomeomorph P n
      (orderVertex _ (iteratedOrderSubdivisionVertex P n p)) = orderVertex P p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    letI := iteratedOrderSubdivisionFintype P n
    rw [iteratedOrderSubdivisionHomeomorph_succ]
    change iteratedOrderSubdivisionHomeomorph P n
      (orderSubdivisionHomeomorph _ (orderVertex _
        (orderSingletonChain (iteratedOrderSubdivisionVertex P n p)))) = _
    rw [orderSubdivisionHomeomorph_singleton_vertex]
    exact ih

end KIP126.Topology.SimplicialRealization
