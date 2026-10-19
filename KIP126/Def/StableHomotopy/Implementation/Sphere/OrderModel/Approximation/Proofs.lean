module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OrderModel.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Generators
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Homotopy.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Dimension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization
open scoped unitInterval Classical
set_option backward.isDefEq.respectTransparency false

/-- Every based self-map of the original sphere is based-homotopic to
the actual realization of an order map between finite boundary models.
Both comparison homeomorphisms are constructed from the original sphere;
the target comparison preserves its original basepoint as a vertex. -/
theorem exists_sphere_map_order_approximation (n : ℕ)
    (f : sphereLevel n ⟶ sphereLevel n) :
    ∃ (k : ℕ) (p : orderProperChains (Fin (n + 2))),
    ∃ e : sphereLevel n ≃ₜ
        |nerve (iteratedOrderSubdivision (orderProperChains (Fin (n + 2))) (k + 1))|,
    ∃ h : sphereLevel n ≃ₜ |nerve (orderProperChains (Fin (n + 2)))|,
    ∃ φ : iteratedOrderSubdivision (orderProperChains (Fin (n + 2))) (k + 1) →o
        orderProperChains (Fin (n + 2)),
      h (sphereLevel n).point = orderVertex _ p ∧
      ∃ g : sphereLevel n ⟶ sphereLevel n,
        Nonempty (ContinuousMap.HomotopyRel g.map f.map {(sphereLevel n).point}) ∧
        ∀ x, h (g.map x) = SSet.toTop.map (nerveMap φ.monotone.functor) (e x) := by
  classical
  let Q := orderProperChains (Fin (n + 2))
  letI := finite_nonemptyFiniteChains (Fin (n + 2))
  letI : Fintype Q := Fintype.ofFinite Q
  let p : Q := ⟨{
    finset := {0}
    nonempty := Finset.singleton_nonempty _
    comparable := fun a b => le_total a.val b.val }, by
      change ({0} : Finset (Fin (n + 2))) ≠ Finset.univ
      intro he
      have hc := congrArg Finset.card he
      simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hc
      omega⟩
  obtain ⟨h, hp⟩ := exists_sphereLevel_orderBoundary_homeomorph n p
  let F : C(|nerve Q|, |nerve Q|) :=
    ⟨fun x => h (f.map (h.symm x)), h.continuous.comp (f.map.continuous.comp h.symm.continuous)⟩
  obtain ⟨k, v, hv⟩ := exists_iteratedOrderSubdivision_star_assignment Q Q F
  letI := iteratedOrderSubdivisionFintype Q k
  obtain ⟨H, _, hfix⟩ := hv.exists_carrier_homotopy_fixing_vertices
  let φ : iteratedOrderSubdivision Q (k + 1) →o Q :=
    orderCarrierMaximum v hv.preservesOrderChains
  let s := iteratedOrderSubdivisionHomeomorph Q (k + 1)
  let e := h.trans s.symm
  let G : C(sphereLevel n, sphereLevel n) :=
    ⟨fun x => h.symm (SSet.toTop.map (nerveMap φ.monotone.functor) (e x)),
      h.symm.continuous.comp ((SSet.toTop.map (nerveMap φ.monotone.functor)).hom.continuous.comp
        e.continuous)⟩
  have hstart (x : sphereLevel n) :
      (F.comp ⟨iteratedOrderSubdivisionHomeomorph Q k,
        (iteratedOrderSubdivisionHomeomorph Q k).continuous⟩)
        (orderSubdivisionHomeomorph (iteratedOrderSubdivision Q k) (e x)) = h (f.map x) := by
    change F (s (e x)) = _
    change h (f.map (h.symm (s (s.symm (h x))))) = _
    rw [s.apply_symm_apply, h.symm_apply_apply]
  have hHp (t : I) : H (t, e (sphereLevel n).point) = orderVertex Q p := by
    apply hfix
    rw [hstart, f.point, hp]
  have hGp : G (sphereLevel n).point = (sphereLevel n).point := by
    change h.symm (SSet.toTop.map (orderCarrierSimplicialMap v hv.preservesOrderChains)
      (e (sphereLevel n).point)) = _
    rw [← H.apply_one (e (sphereLevel n).point), hHp, ← hp, h.symm_apply_apply]
  let g : sphereLevel n ⟶ sphereLevel n := ⟨G, hGp⟩
  have HG : Nonempty (ContinuousMap.HomotopyRel f.map g.map {(sphereLevel n).point}) := by
    refine ⟨{
      toFun := fun z => h.symm (H (z.1, e z.2))
      continuous_toFun := h.symm.continuous.comp (H.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro x
      rw [H.apply_zero]
      change h.symm ((F.comp ⟨iteratedOrderSubdivisionHomeomorph Q k,
        (iteratedOrderSubdivisionHomeomorph Q k).continuous⟩)
        (orderSubdivisionHomeomorph (iteratedOrderSubdivision Q k) (e x))) = _
      rw [hstart, h.symm_apply_apply]
    · intro x
      rw [H.apply_one]
      rfl
    · intro t x hx
      have hx' : x = (sphereLevel n).point := Set.mem_singleton_iff.mp hx
      subst x
      change h.symm (H (t, e (sphereLevel n).point)) = f.map (sphereLevel n).point
      exact (congrArg h.symm (hHp t)).trans
        ((congrArg h.symm hp.symm).trans ((h.symm_apply_apply _).trans f.point.symm))
  refine ⟨k, p, e, h, φ, hp, g, ⟨HG.some.symm⟩, ?_⟩
  intro x
  exact h.apply_symm_apply _

end KIP126.StableHomotopy.Implementation.Prespectrum
