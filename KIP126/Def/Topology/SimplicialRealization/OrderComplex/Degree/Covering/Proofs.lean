module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularStar.Homeomorph.Proofs
public import Mathlib.Topology.Covering.Basic

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false

/-- Over full-dimensional target simplex interiors, the original
realized order map is an actual local homeomorphism. -/
theorem orderMap_isLocalHomeomorphOn_full_support {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (hQ : OrderChainSizeLE Q N) :
    IsLocalHomeomorphOn (SSet.toTop.map (nerveMap f.monotone.functor))
      {x | (positiveSupport (orderComplexCoordinates Q
        (SSet.toTop.map (nerveMap f.monotone.functor) x))).card = N} := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro x hx
  obtain ⟨hc, hf⟩ := orderMap_full_support_preimage f N hP x hx
  let c : PartialOrder.NonemptyFiniteChains P := {
    finset := positiveSupport (orderComplexCoordinates P x)
    nonempty := by
      obtain ⟨p, hp⟩ := simplex_exists_positive (orderComplexCoordinates P x)
      exact ⟨p, (mem_positiveSupport _ _).mpr hp⟩
    comparable := fun p q => orderComplexCoordinates_hasChainSupport P x p.val q.val
      ((mem_positiveSupport _ _).mp p.property) ((mem_positiveSupport _ _).mp q.property) }
  obtain ⟨e, he⟩ := exists_orderMap_full_star_homeomorph f N hP hQ c hc hf
  refine ⟨orderOpenStarIntersection P c.finset,
    (isOpen_orderOpenStarIntersection P c.finset).mem_nhds ?_, ?_⟩
  · intro p hp
    exact (mem_positiveSupport _ _).mp hp
  · have h := (isOpen_orderOpenStarIntersection Q (c.finset.image f)).isOpenEmbedding_subtypeVal.comp
      e.isOpenEmbedding
    convert h using 1
    funext z
    exact (he z).symm

/-- Compactness and the proved actual local charts make the original
realized order map a genuine covering over all full-dimensional target
simplex interiors. Empty fibers are permitted. -/
theorem orderMap_isCoveringMapOn_full_support {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (hQ : OrderChainSizeLE Q N) :
    IsCoveringMapOn (SSet.toTop.map (nerveMap f.monotone.functor))
      {y | (positiveSupport (orderComplexCoordinates Q y)).card = N} := by
  letI := finite_nerve_of_finite_order P
  letI := compactSpace_of_finite (nerve P)
  letI := (exists_orderComplexCoordinates_homeomorph P).choose.isEmbedding.t2Space
  letI := (exists_orderComplexCoordinates_homeomorph Q).choose.isEmbedding.t2Space
  exact IsCoveringMapOn.of_isLocalHomeomorphOn
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom.continuous
    (orderMap_isLocalHomeomorphOn_full_support f N hP hQ)

end KIP126.Topology.SimplicialRealization
