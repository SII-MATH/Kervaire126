module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Simplex.Proofs
public import KIP126.Def.Topology.Simplex.AffineIndependent.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual nondegenerate simplex of an iterated barycentric
subdivision has affinely independent geometric vertices whenever the
original specified vector realization is injective. -/
theorem iteratedOrderSubdivisionVertices_affineIndependent
    (P : Type u) [PartialOrder P] [Fintype P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : P → E)
    (hv : Function.Injective (fun x : |nerve P| => ∑ p, orderComplexCoordinates P x p • v p))
    (n d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (op ⦋d⦌))
    (hs : Function.Injective s.obj) :
    AffineIndependent ℝ (fun k => iteratedOrderSubdivisionVertices v n (s.obj k)) := by
  letI := iteratedOrderSubdivisionFintype P n
  apply Simplex.affineIndependent_of_injective_simplex_sum
  intro t w htw
  have hx : simplexPoint _ s t = simplexPoint _ s w := by
    apply (iteratedOrderSubdivisionHomeomorph P n).injective
    apply hv
    dsimp only
    rw [iteratedOrderSubdivisionHomeomorph_simplex_sum_smul,
      iteratedOrderSubdivisionHomeomorph_simplex_sum_smul]
    exact htw
  have hcoords := congrArg (orderComplexCoordinates (iteratedOrderSubdivision P n)) hx
  rw [orderComplexCoordinates_simplex, orderComplexCoordinates_simplex] at hcoords
  exact simplex_map_injective s.obj hs hcoords

/-- In the actual coordinate embedding of every finite order complex,
all actual nondegenerate simplices of every iterated subdivision have
affinely independent recursively averaged vertices. -/
theorem iteratedOrderSubdivision_coordinateVertices_affineIndependent
    (P : Type u) [PartialOrder P] [Fintype P]
    (n d : ℕ) (s : (nerve (iteratedOrderSubdivision P n)).obj (op ⦋d⦌))
    (hs : Function.Injective s.obj) :
    AffineIndependent ℝ (fun k => iteratedOrderSubdivisionVertices
      (fun p : P => Pi.single p (1 : ℝ)) n (s.obj k)) := by
  apply iteratedOrderSubdivisionVertices_affineIndependent P _ ?_ n d s hs
  intro x y hxy
  apply orderComplexCoordinates_injective P
  apply stdSimplex.ext
  funext p
  have h := congrFun hxy p
  simpa [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] using h

/-- The actual proper-chain boundary realization evaluates in its
original simplex vertices as the sum of its chain-barycenter vectors. -/
theorem orderBoundary_sum_smul_barycenter (P : Type u) [PartialOrder P] [Fintype P]
    [Fintype (orderProperChains P)] (x : |nerve (orderProperChains P)|) :
    (∑ c, orderComplexCoordinates (orderProperChains P) x c •
      (fun p => orderChainBarycenter P c.val p)) =
      (fun p => orderSubdivisionCoordinates P (SSet.toTop.map (orderBoundaryInclusion P) x) p) := by
  obtain ⟨d, s, w, _, _, hx⟩ := exists_orderComplex_positive_simplex (orderProperChains P) x
  rw [← hx, orderComplexCoordinates_simplex, Simplex.sum_smul_map]
  rw [simplexPoint_map, orderSubdivisionCoordinates_simplex]
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The actual barycentric vectors of every nondegenerate simplex in
every iterated subdivision of a standard-simplex boundary are affinely
independent. This follows from its proved actual geometric homeomorphism. -/
theorem iteratedOrderBoundaryVertices_affineIndependent
    (P : Type u) [LinearOrder P] [Fintype P]
    (n d : ℕ) (s : (nerve (iteratedOrderSubdivision (orderProperChains P) n)).obj (op ⦋d⦌))
    (hs : Function.Injective s.obj) :
    AffineIndependent ℝ (fun k => iteratedOrderSubdivisionVertices
      (fun c : orderProperChains P => fun p => orderChainBarycenter P c.val p) n (s.obj k)) := by
  letI := finite_nonemptyFiniteChains P
  letI : Fintype (orderProperChains P) := Fintype.ofFinite _
  apply iteratedOrderSubdivisionVertices_affineIndependent (orderProperChains P) _ ?_ n d s hs
  intro x y hxy
  dsimp only at hxy
  rw [orderBoundary_sum_smul_barycenter, orderBoundary_sum_smul_barycenter] at hxy
  obtain ⟨e, he⟩ := exists_orderBoundary_stdSimplex_homeomorph P
  apply e.injective
  apply Subtype.ext
  rw [he, he]
  exact stdSimplex.ext hxy

end KIP126.Topology.SimplicialRealization
