module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs

@[expose] public section

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- The actual iterated simplicial last-vertex comparison, with the same
subdivision objects as the actual barycentric homeomorphism. -/
noncomputable def iteratedOrderSubdivisionLastVertex (P : Type u) [PartialOrder P] :
    (n : ℕ) → (nerve (iteratedOrderSubdivision P n) ⟶ nerve P) := fun n => match n with
  | 0 => 𝟙 _
  | n+1 => orderSubdivisionLastVertex (iteratedOrderSubdivision P n) ≫
      iteratedOrderSubdivisionLastVertex P n

end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- The chosen actual barycentric homeomorphism is homotopic to its
actual simplicial last-vertex comparison. -/
theorem orderSubdivisionHomeomorph_homotopic_lastVertex (P : Type u)
    [PartialOrder P] [Fintype P] :
    (⟨orderSubdivisionHomeomorph P,(orderSubdivisionHomeomorph P).continuous⟩ :
      C(|nerve (PartialOrder.NonemptyFiniteChains P)|,|nerve P|)).Homotopic
        (SSet.toTop.map (orderSubdivisionLastVertex P)).hom := by
  obtain ⟨h,hh,H,_⟩ := exists_orderSubdivision_homeomorph_homotopy P
  have he : h = orderSubdivisionHomeomorph P := by
    apply Homeomorph.ext
    intro x
    apply orderComplexCoordinates_injective P
    rw [hh,orderSubdivisionHomeomorph_coordinates]
  subst h
  exact ⟨H⟩

/-- Every iterated geometric subdivision comparison is homotopic to a
genuine simplicial map with the same source and target. -/
theorem iteratedOrderSubdivisionHomeomorph_homotopic_lastVertex (P : Type u)
    [PartialOrder P] [Fintype P] (n : ℕ) :
    (⟨iteratedOrderSubdivisionHomeomorph P n,
      (iteratedOrderSubdivisionHomeomorph P n).continuous⟩ :
      C(|nerve (iteratedOrderSubdivision P n)|,|nerve P|)).Homotopic
        (SSet.toTop.map (iteratedOrderSubdivisionLastVertex P n)).hom := by
  induction n with
  | zero =>
    change (ContinuousMap.id |nerve P|).Homotopic (SSet.toTop.map (𝟙 (nerve P))).hom
    rw [CategoryTheory.Functor.map_id]
    exact ContinuousMap.Homotopic.refl _
  | succ n ih =>
    letI := iteratedOrderSubdivisionFintype P n
    have h := ih.comp (orderSubdivisionHomeomorph_homotopic_lastVertex
      (iteratedOrderSubdivision P n))
    convert h using 1 <;> try rfl
    apply ContinuousMap.ext
    intro x
    rw [iteratedOrderSubdivisionLastVertex,CategoryTheory.Functor.map_comp,TopCat.comp_app]
    rfl

end KIP126.Topology.SimplicialRealization

end
