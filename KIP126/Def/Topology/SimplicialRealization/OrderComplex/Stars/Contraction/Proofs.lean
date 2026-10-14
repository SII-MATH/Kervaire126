module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The common open star of a nonempty chain has an actual straight-line
contraction to its uniform barycenter, transported through the proved
coordinate homeomorphism. The center is fixed throughout. -/
theorem exists_orderOpenStarIntersection_contraction (P : Type u)
    [PartialOrder P] [Fintype P] (c : PartialOrder.NonemptyFiniteChains P) :
    ∃ b : orderOpenStarIntersection P c.finset,
      orderComplexCoordinates P b.val = orderChainBarycenter P c ∧
      ∃ H : (ContinuousMap.id (orderOpenStarIntersection P c.finset)).Homotopy
          (ContinuousMap.const _ b),
        (∀ (t : I) (x : orderOpenStarIntersection P c.finset) (p : P),
          orderComplexCoordinates P (H (t,x)).val p =
            (1 - (t : ℝ)) * orderComplexCoordinates P x.val p +
              (t : ℝ) * orderChainBarycenter P c p) ∧
        ∀ t : I, H (t,b) = b := by
  obtain ⟨b,hb⟩ := exists_orderOpenStarIntersection_barycenter P c
  obtain ⟨e,he⟩ := exists_orderComplexCoordinates_homeomorph P
  have hei (y : {y : stdSimplex ℝ P // HasChainSupport y}) :
      orderComplexCoordinates P (e.symm y) = y.val := by
    have h := he (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  let a : C(orderOpenStarIntersection P c.finset,stdSimplex ℝ P) :=
    ⟨fun x => orderComplexCoordinates P x.val,
      (orderComplexCoordinates P).continuous.comp continuous_subtype_val⟩
  obtain ⟨G,hG⟩ := Simplex.exists_affine_homotopy a
    (ContinuousMap.const _ (orderChainBarycenter P c))
  have hformula (t : I) (x : orderOpenStarIntersection P c.finset) (p : P) :
      G (t,x) p = (1 - (t : ℝ)) * orderComplexCoordinates P x.val p +
        (t : ℝ) * orderChainBarycenter P c p := hG t x p
  have hzero (t : I) (x : orderOpenStarIntersection P c.finset) (p : P)
      (hx : orderComplexCoordinates P x.val p = 0) : G (t,x) p = 0 := by
    have hp : p ∉ c.finset := fun hp => (ne_of_gt (x.property p hp)) hx
    rw [hformula,hx,orderChainBarycenter_apply,if_neg hp]
    simp
  have hchain (t : I) (x : orderOpenStarIntersection P c.finset) :
      HasChainSupport (G (t,x)) := by
    intro p q hp hq
    apply orderComplexCoordinates_hasChainSupport P x.val p q
    · exact lt_of_le_of_ne ((orderComplexCoordinates P x.val).property.1 p)
        (fun h => (ne_of_gt hp) (hzero t x p h.symm))
    · exact lt_of_le_of_ne ((orderComplexCoordinates P x.val).property.1 q)
        (fun h => (ne_of_gt hq) (hzero t x q h.symm))
  have hpos (t : I) (x : orderOpenStarIntersection P c.finset) (p : P)
      (hp : p ∈ c.finset) : 0 < G (t,x) p := by
    rw [hformula]
    have hx : 0 < orderComplexCoordinates P x.val p := x.property p hp
    have hbp : 0 < orderChainBarycenter P c p := by
      rw [orderChainBarycenter_apply,if_pos hp]
      exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr c.nonempty))
    obtain ht | ht := lt_or_eq_of_le t.property.1
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) hx.le) (mul_pos ht hbp)
    · rw [← ht]
      simpa using hx
  let H : (ContinuousMap.id (orderOpenStarIntersection P c.finset)).Homotopy
      (ContinuousMap.const _ b) := {
    toFun := fun z => ⟨e.symm ⟨G z,hchain z.1 z.2⟩,by
      intro p hp
      change 0 < orderComplexCoordinates P (e.symm ⟨G z,hchain z.1 z.2⟩) p
      rw [hei]
      exact hpos z.1 z.2 p hp⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact e.symm.continuous.comp (G.continuous.subtype_mk (fun z => hchain z.1 z.2))
    map_zero_left := by
      intro x
      apply Subtype.ext
      apply orderComplexCoordinates_injective P
      rw [hei]
      exact G.apply_zero x
    map_one_left := by
      intro x
      apply Subtype.ext
      apply orderComplexCoordinates_injective P
      rw [hei]
      exact (G.apply_one x).trans hb.symm }
  have hH (t : I) (x : orderOpenStarIntersection P c.finset) (p : P) :
      orderComplexCoordinates P (H (t,x)).val p =
        (1 - (t : ℝ)) * orderComplexCoordinates P x.val p +
          (t : ℝ) * orderChainBarycenter P c p := by
    change orderComplexCoordinates P (e.symm ⟨G (t,x),hchain t x⟩) p = _
    rw [hei]
    exact hformula t x p
  refine ⟨b,hb,H,hH,?_⟩
  intro t
  apply Subtype.ext
  apply orderComplexCoordinates_injective P
  apply stdSimplex.ext
  funext p
  change orderComplexCoordinates P (H (t,b)).val p = orderComplexCoordinates P b.val p
  rw [hH,hb]
  ring

/-- Every common open star indexed by a nonempty actual chain is contractible. -/
theorem orderOpenStarIntersection_contractibleSpace (P : Type u)
    [PartialOrder P] [Fintype P] (c : PartialOrder.NonemptyFiniteChains P) :
    ContractibleSpace (orderOpenStarIntersection P c.finset) := by
  obtain ⟨b,_,H,_,_⟩ := exists_orderOpenStarIntersection_contraction P c
  exact (contractible_iff_id_nullhomotopic _).mpr ⟨b,⟨H⟩⟩

/-- Each actual vertex's open star is contractible. -/
theorem orderOpenStar_contractibleSpace (P : Type u)
    [PartialOrder P] [Fintype P] (p : P) : ContractibleSpace (orderOpenStar P p) := by
  let c : PartialOrder.NonemptyFiniteChains P := {
    finset := {p}
    nonempty := Finset.singleton_nonempty p
    comparable := by
      intro a b
      have ha : a.val = p := Finset.mem_singleton.mp a.property
      have hb : b.val = p := Finset.mem_singleton.mp b.property
      exact Or.inl (ha.trans hb.symm).le }
  have he : orderOpenStarIntersection P c.finset = orderOpenStar P p := by
    ext x
    simp [orderOpenStarIntersection,c]
  rw [← he]
  exact orderOpenStarIntersection_contractibleSpace P c

end KIP126.Topology.SimplicialRealization
