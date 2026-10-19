module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularStar.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual order maps carry the common star of source vertices into
the common star of their images. -/
theorem orderMap_mapsTo_openStarIntersection {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (s : Finset P) :
    Set.MapsTo (SSet.toTop.map (nerveMap f.monotone.functor))
      (orderOpenStarIntersection P s) (orderOpenStarIntersection Q (s.image f)) := by
  intro x hx q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  change 0 < orderComplexCoordinates Q (SSet.toTop.map (nerveMap f.monotone.functor) x) (f p)
  rw [orderComplexCoordinates_natural]
  apply (mem_positiveSupport _ _).mp
  rw [positiveSupport_map]
  exact Finset.mem_image.mpr ⟨p, (mem_positiveSupport _ _).mpr (hx p hp), rfl⟩

/-- On an injectively mapped full-dimensional chain, every point of
the target common star has a preimage in the original source common star. -/
theorem orderMap_full_star_surjective {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hQ : OrderChainSizeLE Q N)
    (c : PartialOrder.NonemptyFiniteChains P) (hc : c.finset.card = N)
    (hf : Set.InjOn f c.finset) (y : |nerve Q|)
    (hy : y ∈ orderOpenStarIntersection Q (c.finset.image f)) :
    ∃ x ∈ orderOpenStarIntersection P c.finset,
      SSet.toTop.map (nerveMap f.monotone.functor) x = y := by
  classical
  let w := orderComplexCoordinates Q y
  have hcard : (c.finset.image f).card = N := (Finset.card_image_of_injOn hf).trans hc
  have hsupport : positiveSupport w = c.finset.image f :=
    orderOpenStarIntersection_positiveSupport_eq Q N hQ _ hcard y hy
  have hwzero (q : Q) (hq : q ∉ c.finset.image f) : w q = 0 := by
    apply le_antisymm _ (stdSimplex.zero_le w q)
    apply le_of_not_gt
    intro hp
    exact hq (hsupport ▸ (mem_positiveSupport _ _).mpr hp)
  have hsum : ∑ p : P, (if p ∈ c.finset then w (f p) else 0) = 1 := by
    calc
      _ = ∑ p ∈ c.finset, w (f p) := by simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = ∑ q ∈ c.finset.image f, w q := (Finset.sum_image hf).symm
      _ = ∑ q : Q, w q := Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hwzero q hq)
      _ = 1 := stdSimplex.sum_eq_one w
  let v : stdSimplex ℝ P := ⟨fun p => if p ∈ c.finset then w (f p) else 0,
    (fun p => by dsimp only; split_ifs <;> simp [stdSimplex.zero_le]), hsum⟩
  have hv : positiveSupport v = c.finset := by
    ext p
    rw [mem_positiveSupport]
    change (0 < if p ∈ c.finset then w (f p) else 0) ↔ p ∈ c.finset
    by_cases hp : p ∈ c.finset
    · rw [if_pos hp]
      exact ⟨fun _ => hp, fun _ => (mem_positiveSupport w (f p)).mp
        (hsupport.symm ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩
    · simp [hp]
  have hchain : HasChainSupport v := by
    intro p q hp hq
    exact c.comparable ⟨p, hv ▸ (mem_positiveSupport _ _).mpr hp⟩
      ⟨q, hv ▸ (mem_positiveSupport _ _).mpr hq⟩
  have hvmap : stdSimplex.map f v = w := by
    apply stdSimplex.ext
    funext q
    by_cases hq : q ∈ c.finset.image f
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      rw [map_apply_of_injOn_positiveSupport f v (hv.symm ▸ hf) p (hv.symm ▸ hp)]
      exact if_pos hp
    · have hzero : stdSimplex.map f v q = 0 := by
        apply le_antisymm _ (stdSimplex.zero_le _ _)
        apply le_of_not_gt
        intro hpos
        have hh := (mem_positiveSupport (stdSimplex.map f v) q).mpr hpos
        rw [positiveSupport_map, hv] at hh
        exact hq hh
      exact hzero.trans (hwzero q hq).symm
  obtain ⟨x, hx⟩ := orderComplexCoordinates_preimage P v hchain
  refine ⟨x, ?_, ?_⟩
  · intro p hp
    change 0 < orderComplexCoordinates P x p
    rw [hx]
    exact (mem_positiveSupport _ _).mp (hv.symm ▸ hp)
  · apply orderComplexCoordinates_injective Q
    rw [orderComplexCoordinates_natural, hx]
    exact hvmap

/-- A full-dimensional source chain mapped injectively on vertices gives
an actual homeomorphism of the two open simplex interiors, with the
original realized simplicial map as its forward function. -/
theorem exists_orderMap_full_star_homeomorph {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (hQ : OrderChainSizeLE Q N)
    (c : PartialOrder.NonemptyFiniteChains P) (hc : c.finset.card = N)
    (hf : Set.InjOn f c.finset) :
    ∃ h : (orderOpenStarIntersection P c.finset) ≃ₜ
        (orderOpenStarIntersection Q (c.finset.image f)),
      ∀ x, (h x).val = SSet.toTop.map (nerveMap f.monotone.functor) x.val := by
  let g : (orderOpenStarIntersection P c.finset) →
      (orderOpenStarIntersection Q (c.finset.image f)) := fun x =>
    ⟨SSet.toTop.map (nerveMap f.monotone.functor) x.val,
      orderMap_mapsTo_openStarIntersection f c.finset x.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x z hxz
      apply Subtype.ext
      apply orderComplexCoordinates_injective P
      apply stdSimplex.ext
      funext p
      rw [orderMap_full_star_coordinate_inverse f N hP c.finset hc hf x.val x.property p,
        orderMap_full_star_coordinate_inverse f N hP c.finset hc hf z.val z.property p]
      exact congrArg (fun y : (orderOpenStarIntersection Q (c.finset.image f)) =>
        if p ∈ c.finset then orderComplexCoordinates Q y.val (f p) else 0) hxz
    · intro y
      obtain ⟨x, hx, hxy⟩ := orderMap_full_star_surjective f N hQ c hc hf y.val y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := Equiv.ofBijective g hg
  have hgcont : Continuous g :=
    ((SSet.toTop.map (nerveMap f.monotone.functor)).hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hcoords : Continuous (fun y => orderComplexCoordinates P (e.symm y).val) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro p
    have heq : (fun y => orderComplexCoordinates P (e.symm y).val p) =
        (fun y => if p ∈ c.finset then orderComplexCoordinates Q y.val (f p) else 0) := by
      funext y
      rw [orderMap_full_star_coordinate_inverse f N hP c.finset hc hf
        (e.symm y).val (e.symm y).property p]
      exact congrArg (fun z : (orderOpenStarIntersection Q (c.finset.image f)) =>
        if p ∈ c.finset then orderComplexCoordinates Q z.val (f p) else 0) (e.apply_symm_apply y)
    have hh : Continuous (fun y : (orderOpenStarIntersection Q (c.finset.image f)) =>
        if p ∈ c.finset then orderComplexCoordinates Q y.val (f p) else 0) := by
      split_ifs
      · exact (continuous_apply (f p)).comp
          ((orderComplexCoordinates Q).continuous.subtype_val.comp continuous_subtype_val)
      · exact continuous_const
    exact heq.symm ▸ hh
  obtain ⟨ep, hep⟩ := exists_orderComplexCoordinates_homeomorph P
  have hepc : Continuous (fun y => ep (e.symm y).val) := by
    apply Continuous.subtype_mk
    convert hcoords using 1
    funext y
    exact hep _
  have hinv : Continuous (fun y => (e.symm y).val) := by
    convert ep.symm.continuous.comp hepc using 1
    funext y
    exact (ep.symm_apply_apply _).symm
  exact ⟨{
    toEquiv := e
    continuous_toFun := hgcont
    continuous_invFun := hinv.subtype_mk _ }, fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
