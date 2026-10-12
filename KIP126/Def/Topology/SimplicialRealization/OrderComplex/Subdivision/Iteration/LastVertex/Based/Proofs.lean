module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.LastVertex
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Vertices
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Carrier.Homotopy.Proofs
public import KIP126.Def.Topology.Homotopy.Precomposition.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual last-vertex comparison homotopy fixes the original
specified vertex throughout its singleton-chain preimage. -/
theorem orderSubdivisionHomeomorph_homotopicRel_lastVertex (P : Type u)
    [PartialOrder P] [Fintype P] (p : P) :
    (⟨orderSubdivisionHomeomorph P,(orderSubdivisionHomeomorph P).continuous⟩ :
      C(|nerve (PartialOrder.NonemptyFiniteChains P)|,|nerve P|)).HomotopicRel
        (SSet.toTop.map (orderSubdivisionLastVertex P)).hom
        {orderVertex _ (orderSingletonChain p)} := by
  obtain ⟨h,hh,H,hzero⟩ := exists_orderSubdivision_homeomorph_homotopy P
  have he : h = orderSubdivisionHomeomorph P := by
    apply Homeomorph.ext
    intro x
    apply orderComplexCoordinates_injective P
    rw [hh,orderSubdivisionHomeomorph_coordinates]
  subst h
  refine ⟨⟨H,?_⟩⟩
  rintro t x rfl
  change H (t,orderVertex _ (orderSingletonChain p)) =
    orderSubdivisionHomeomorph P (orderVertex _ (orderSingletonChain p))
  rw [orderSubdivisionHomeomorph_singleton_vertex]
  apply eq_orderVertex_of_zero_coordinates P _ p
  intro q hq
  apply hzero t _ q
  rw [← orderSubdivisionHomeomorph_coordinates,orderSubdivisionHomeomorph_singleton_vertex,
    orderComplexCoordinates_vertex]
  simp [stdSimplex.vertex,hq]

/-- The genuine iterated subdivision comparison is homotopic to the
actual iterated simplicial last-vertex map relative to the given
original vertex at every depth. -/
theorem iteratedOrderSubdivisionHomeomorph_homotopicRel_lastVertex (P : Type u)
    [PartialOrder P] [Fintype P] (n : ℕ) (p : P) :
    (⟨iteratedOrderSubdivisionHomeomorph P n,
      (iteratedOrderSubdivisionHomeomorph P n).continuous⟩ :
      C(|nerve (iteratedOrderSubdivision P n)|,|nerve P|)).HomotopicRel
        (SSet.toTop.map (iteratedOrderSubdivisionLastVertex P n)).hom
        {orderVertex _ (iteratedOrderSubdivisionVertex P n p)} := by
  induction n with
  | zero =>
    change (ContinuousMap.id |nerve P|).HomotopicRel
      (SSet.toTop.map (𝟙 (nerve P))).hom {orderVertex P p}
    rw [CategoryTheory.Functor.map_id]
    exact ContinuousMap.HomotopicRel.refl _
  | succ n ih =>
    letI := iteratedOrderSubdivisionFintype P n
    let r := iteratedOrderSubdivisionVertex P n p
    let s := orderVertex _ (orderSingletonChain r)
    let ℓ := orderSubdivisionLastVertex (iteratedOrderSubdivision P n)
    let ec : C(|nerve (iteratedOrderSubdivision P n)|,|nerve P|) :=
      ⟨iteratedOrderSubdivisionHomeomorph P n,
        (iteratedOrderSubdivisionHomeomorph P n).continuous⟩
    have hs := orderSubdivisionHomeomorph_homotopicRel_lastVertex
      (iteratedOrderSubdivision P n) r
    have hℓ : SSet.toTop.map ℓ s = orderVertex _ r := by
      obtain ⟨G⟩ := hs
      exact (G.apply_one s).symm.trans ((G.eq_fst 1 rfl).trans
        (orderSubdivisionHomeomorph_singleton_vertex _ r))
    have h₀ := hs.comp_continuousMap ec
    have h₁ := homotopicRel_precomp ih (SSet.toTop.map ℓ).hom (T := {s})
      (by rintro x rfl; exact hℓ)
    have h := h₀.trans h₁
    convert h using 1 <;> try rfl
    apply ContinuousMap.ext
    intro x
    rw [iteratedOrderSubdivisionLastVertex,CategoryTheory.Functor.map_comp,TopCat.comp_app]
    rfl

end KIP126.Topology.SimplicialRealization
