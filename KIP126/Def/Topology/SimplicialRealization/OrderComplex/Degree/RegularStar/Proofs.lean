module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularFiber.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical
universe u

/-- A full-dimensional common open star has exactly its specified
positive-coordinate support; no additional source vertices can occur. -/
theorem orderOpenStarIntersection_positiveSupport_eq
    (P : Type u) [PartialOrder P] [Fintype P] (N : ℕ)
    (hP : OrderChainSizeLE P N) (s : Finset P) (hs : s.card = N)
    (x : |nerve P|) (hx : x ∈ orderOpenStarIntersection P s) :
    positiveSupport (orderComplexCoordinates P x) = s := by
  have hsub : s ⊆ positiveSupport (orderComplexCoordinates P x) := by
    intro p hp
    exact (mem_positiveSupport _ _).mpr (hx p hp)
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [hs]
    exact orderComplexCoordinates_positiveSupport_card_le P N hP x)).symm

/-- At an actual preimage of a full-dimensional target point, the source
support is full-dimensional and its vertex map is injective. -/
theorem orderMap_full_support_preimage {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N)
    (x : |nerve P|)
    (hx : (positiveSupport (orderComplexCoordinates Q
      (SSet.toTop.map (nerveMap f.monotone.functor) x))).card = N) :
    (positiveSupport (orderComplexCoordinates P x)).card = N ∧
      Set.InjOn f (positiveSupport (orderComplexCoordinates P x)) := by
  classical
  have him : ((positiveSupport (orderComplexCoordinates P x)).image f).card = N := by
    rw [← positiveSupport_map, ← orderComplexCoordinates_natural]
    exact hx
  have hc : (positiveSupport (orderComplexCoordinates P x)).card = N :=
    le_antisymm (orderComplexCoordinates_positiveSupport_card_le P N hP x)
      (by rw [← him]; exact Finset.card_image_le)
  exact ⟨hc, Finset.injOn_of_card_image_eq (him.trans hc.symm)⟩

/-- On a full-dimensional source star with injective vertex map, the
original source coordinates are recovered directly from target coordinates. -/
theorem orderMap_full_star_coordinate_inverse {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N)
    (s : Finset P) (hs : s.card = N) (hf : Set.InjOn f s)
    (x : |nerve P|) (hx : x ∈ orderOpenStarIntersection P s) (p : P) :
    orderComplexCoordinates P x p = if p ∈ s then
      orderComplexCoordinates Q (SSet.toTop.map (nerveMap f.monotone.functor) x) (f p) else 0 := by
  have hsupport := orderOpenStarIntersection_positiveSupport_eq P N hP s hs x hx
  by_cases hp : p ∈ s
  · rw [if_pos hp, orderComplexCoordinates_natural]
    exact (map_apply_of_injOn_positiveSupport f (orderComplexCoordinates P x)
      (hsupport.symm ▸ hf) p (hsupport.symm ▸ hp)).symm
  · rw [if_neg hp]
    have hn : ¬ 0 < orderComplexCoordinates P x p := by
      intro h
      exact hp (hsupport ▸ (mem_positiveSupport _ _).mpr h)
    exact le_antisymm (le_of_not_gt hn) (stdSimplex.zero_le _ _)

/-- Each preimage of a full-dimensional target interior point has an
actual open neighborhood on which the realized simplicial map is injective. -/
theorem orderMap_locally_injective_of_full_support {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (x : |nerve P|)
    (hx : (positiveSupport (orderComplexCoordinates Q
      (SSet.toTop.map (nerveMap f.monotone.functor) x))).card = N) :
    ∃ U : Set |nerve P|, IsOpen U ∧ x ∈ U ∧
      Set.InjOn (SSet.toTop.map (nerveMap f.monotone.functor)) U := by
  let s := positiveSupport (orderComplexCoordinates P x)
  obtain ⟨hs, hf⟩ := orderMap_full_support_preimage f N hP x hx
  refine ⟨orderOpenStarIntersection P s, isOpen_orderOpenStarIntersection P s, ?_, ?_⟩
  · intro p hp
    exact (mem_positiveSupport _ _).mp hp
  · intro a ha b hb hab
    apply orderComplexCoordinates_injective P
    apply stdSimplex.ext
    funext p
    rw [orderMap_full_star_coordinate_inverse f N hP s hs hf a ha p,
      orderMap_full_star_coordinate_inverse f N hP s hs hf b hb p, hab]

end KIP126.Topology.SimplicialRealization
