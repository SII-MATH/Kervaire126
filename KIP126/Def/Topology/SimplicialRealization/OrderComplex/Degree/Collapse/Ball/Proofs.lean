module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.Collapse.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularStar.Euclidean.Proofs
public import KIP126.Def.Topology.Collapse.Covering.Euclidean.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual order map has a genuine finite collection of disjoint
Euclidean sheets above a Euclidean neighborhood of a full-dimensional
target point. The neighborhood avoids the specified basepoint image. -/
theorem exists_orderMap_full_support_ball_chart
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (n : ℕ)
    (hP : OrderChainSizeLE P (n + 1)) (hQ : OrderChainSizeLE Q (n + 1))
    (y : |nerve Q|)
    (hy : (positiveSupport (orderComplexCoordinates Q y)).card = n + 1)
    (x₀ : |nerve P|)
    (hxy : SSet.toTop.map (nerveMap f.monotone.functor) x₀ ≠ y) :
    Finite {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y} ∧
    ∃ V : Set |nerve Q|, y ∈ V ∧ IsOpen V ∧
      SSet.toTop.map (nerveMap f.monotone.functor) x₀ ∉ V ∧
      Nonempty (V ≃ₜ (Fin n → ℝ)) ∧
      ∃ H : ((SSet.toTop.map (nerveMap f.monotone.functor)) ⁻¹' V) ≃ₜ
          V × {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y},
        ∀ x, (H x).1.val = SSet.toTop.map (nerveMap f.monotone.functor) x.val := by
  letI := (exists_orderComplexCoordinates_homeomorph Q).choose.isEmbedding.t2Space
  let c : PartialOrder.NonemptyFiniteChains Q := {
    finset := positiveSupport (orderComplexCoordinates Q y)
    nonempty := by
      obtain ⟨q, hq⟩ := simplex_exists_positive (orderComplexCoordinates Q y)
      exact ⟨q, (mem_positiveSupport _ _).mpr hq⟩
    comparable := fun p q => orderComplexCoordinates_hasChainSupport Q y p.val q.val
      ((mem_positiveSupport _ _).mp p.property) ((mem_positiveSupport _ _).mp q.property) }
  obtain ⟨e⟩ := exists_orderFullStar_homeomorph_euclidean Q n hQ c hy
  have hyW : y ∈ orderOpenStarIntersection Q c.finset :=
    fun p hp => (mem_positiveSupport _ _).mp hp
  have hcover := orderMap_isCoveringMapOn_full_support f (n + 1) hP hQ y hy
  change IsEvenlyCovered (SSet.toTop.map (nerveMap f.monotone.functor)) y
    {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y} at hcover
  obtain ⟨V, hyV, hV, hVW, heV, _, H, hH⟩ :=
    exists_euclidean_covering_chart_within hcover
      (orderOpenStarIntersection Q c.finset)
      (isOpen_orderOpenStarIntersection Q c.finset) e hyW
      {SSet.toTop.map (nerveMap f.monotone.functor) x₀}ᶜ
      isClosed_singleton.isOpen_compl (Ne.symm hxy)
  exact ⟨finite_orderMap_fiber_of_full_support f (n + 1) hP y hy,
    V, hyV, hV, (fun hx => (hVW hx).1 rfl), heV, H, hH⟩

end KIP126.Topology.SimplicialRealization
