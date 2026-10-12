module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OrderModel.Approximation.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.FullFace.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.Covering.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Every original sphere self-map in positive dimension is
based-homotopic to a map with a genuine finite covering neighborhood at
some nonbasepoint. The finite covering and its actual fiber are proved
from the constructed order approximation, not supplied as hypotheses. -/
theorem exists_sphere_map_homotopic_finite_covering (n : ℕ) (hn : 0 < n)
    (f : sphereLevel n ⟶ sphereLevel n) :
    ∃ g : sphereLevel n ⟶ sphereLevel n,
      Nonempty (ContinuousMap.HomotopyRel g.map f.map {(sphereLevel n).point}) ∧
      ∃ y : sphereLevel n, y ≠ (sphereLevel n).point ∧
        Finite (g.map ⁻¹' {y}) ∧ IsEvenlyCovered g.map y (g.map ⁻¹' {y}) := by
  classical
  obtain ⟨k, p, e, h, φ, hp, g, hg, hφ⟩ := exists_sphere_map_order_approximation n f
  let Q := orderProperChains (Fin (n + 2))
  letI := finite_nonemptyFiniteChains (Fin (n + 2))
  letI : Fintype Q := Fintype.ofFinite Q
  let P := iteratedOrderSubdivision Q (k + 1)
  letI : Fintype P := iteratedOrderSubdivisionFintype Q (k + 1)
  have hQ : OrderChainSizeLE Q (n + 1) := by
    simpa only [Fintype.card_fin, show n + 2 - 1 = n + 1 by omega] using
      orderChainSizeLE_properChains (Fin (n + 2))
  have hP : OrderChainSizeLE P (n + 1) := orderChainSizeLE_iterated Q hQ (k + 1)
  obtain ⟨y, hy, hyp⟩ := exists_orderBoundary_full_support_point n hn p
  let F := SSet.toTop.map (nerveMap φ.monotone.functor)
  let J := F ⁻¹' {y}
  letI : Finite J := finite_orderMap_fiber_of_full_support φ (n + 1) hP y hy
  have hc : IsEvenlyCovered F y J :=
    orderMap_isCoveringMapOn_full_support φ (n + 1) hP hQ y hy
  have ht := (hc.comp_homeomorph e).homeomorph_comp h.symm
  have hfun : h.symm ∘ (F ∘ e) = g.map := by
    funext x
    exact h.symm_apply_eq.mpr (hφ x).symm
  rw [hfun] at ht
  have hy' : h.symm y ≠ (sphereLevel n).point := by
    intro he
    exact hyp ((h.symm_apply_eq.mp he).trans hp)
  letI : Finite (g.map ⁻¹' {h.symm y}) := Finite.of_equiv J ht.fiberHomeomorph.toEquiv
  exact ⟨g, hg, h.symm y, hy', inferInstance, ht.to_isEvenlyCovered_preimage⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
