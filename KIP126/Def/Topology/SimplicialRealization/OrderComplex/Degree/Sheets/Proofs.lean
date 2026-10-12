module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.Sheets.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- The source simplex corresponding to a sheet has its original
vertex map injective. -/
theorem orderFullStarSheet_injOn {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q)
    (s : orderFullStarSheets f c) : Set.InjOn f s.val.finset := by
  apply Finset.injOn_of_card_image_eq
  rw [s.property.2, s.property.1]

/-- The preimage of the specified full-dimensional target open simplex
is partitioned by its actual full source simplices. The sheet is uniquely
the original positive-coordinate support. -/
theorem existsUnique_orderFullStarSheet_of_preimage {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q)
    (hP : OrderChainSizeLE P c.finset.card) (hQ : OrderChainSizeLE Q c.finset.card)
    (x : |nerve P|)
    (hx : SSet.toTop.map (nerveMap f.monotone.functor) x ∈ orderOpenStarIntersection Q c.finset) :
    ∃! s : orderFullStarSheets f c, x ∈ orderOpenStarIntersection P s.val.finset := by
  have ht := orderOpenStarIntersection_positiveSupport_eq Q c.finset.card hQ c.finset rfl
    (SSet.toTop.map (nerveMap f.monotone.functor) x) hx
  have hs := orderMap_full_support_preimage f c.finset.card hP x (congrArg Finset.card ht)
  let s : PartialOrder.NonemptyFiniteChains P := {
    finset := positiveSupport (orderComplexCoordinates P x)
    nonempty := by
      obtain ⟨p, hp⟩ := simplex_exists_positive (orderComplexCoordinates P x)
      exact ⟨p, (mem_positiveSupport _ _).mpr hp⟩
    comparable := fun p q => orderComplexCoordinates_hasChainSupport P x p.val q.val
      ((mem_positiveSupport _ _).mp p.property) ((mem_positiveSupport _ _).mp q.property) }
  have him : s.finset.image f = c.finset := by
    rw [orderComplexCoordinates_natural, Simplex.positiveSupport_map] at ht
    exact ht
  refine ⟨⟨s, hs.1, him⟩, ?_, ?_⟩
  · intro p hp
    exact (mem_positiveSupport _ _).mp hp
  · intro t ht'
    apply Subtype.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    exact (orderOpenStarIntersection_positiveSupport_eq P c.finset.card hP
      t.val.finset t.property.1 x ht').symm

/-- Each actual source sheet maps homeomorphically onto the entire
specified target simplex interior, with the original realized map. -/
theorem exists_orderFullStarSheet_homeomorph {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q)
    (hP : OrderChainSizeLE P c.finset.card) (hQ : OrderChainSizeLE Q c.finset.card)
    (s : orderFullStarSheets f c) :
    ∃ e : orderOpenStarIntersection P s.val.finset ≃ₜ orderOpenStarIntersection Q c.finset,
      ∀ x, (e x).val = SSet.toTop.map (nerveMap f.monotone.functor) x.val := by
  obtain ⟨e, he⟩ := exists_orderMap_full_star_homeomorph f c.finset.card hP hQ s.val
    s.property.1 (orderFullStarSheet_injOn f c s)
  exact ⟨e.trans (Homeomorph.setCongr (congrArg (orderOpenStarIntersection Q) s.property.2)), he⟩

/-- The entire preimage of a full target open simplex is its product
with the finite set of actual source simplices. The comparison retains
the original realized map, the actual source support, and every original
barycentric coordinate; its sheets carry no arbitrary chart choices. -/
theorem exists_orderFullStarSheets_homeomorph {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q)
    (hP : OrderChainSizeLE P c.finset.card) (hQ : OrderChainSizeLE Q c.finset.card) :
    ∃ e : {x : |nerve P| //
        SSet.toTop.map (nerveMap f.monotone.functor) x ∈ orderOpenStarIntersection Q c.finset} ≃ₜ
        orderOpenStarIntersection Q c.finset × orderFullStarSheets f c,
      (∀ x, (e x).1.val = SSet.toTop.map (nerveMap f.monotone.functor) x.val) ∧
      (∀ x, positiveSupport (orderComplexCoordinates P x.val) = (e x).2.val.finset) ∧
      (∀ x p, orderComplexCoordinates P x.val p =
        if p ∈ (e x).2.val.finset then orderComplexCoordinates Q (e x).1.val (f p) else 0) := by
  let F := SSet.toTop.map (nerveMap f.monotone.functor)
  let U : Set |nerve P| := fun x => F x ∈ orderOpenStarIntersection Q c.finset
  let V := orderOpenStarIntersection Q c.finset
  let J := orderFullStarSheets f c
  let j : U → J := fun x => (existsUnique_orderFullStarSheet_of_preimage f c hP hQ x.val x.property).choose
  have hj (x : U) : x.val ∈ orderOpenStarIntersection P (j x).val.finset :=
    (existsUnique_orderFullStarSheet_of_preimage f c hP hQ x.val x.property).choose_spec.1
  have hjuniq (x : U) (s : J) (hx : x.val ∈ orderOpenStarIntersection P s.val.finset) : s = j x :=
    (existsUnique_orderFullStarSheet_of_preimage f c hP hQ x.val x.property).choose_spec.2 s hx
  let q (s : J) := (exists_orderFullStarSheet_homeomorph f c hP hQ s).choose
  have hq (s : J) (x : orderOpenStarIntersection P s.val.finset) : (q s x).val = F x.val :=
    (exists_orderFullStarSheet_homeomorph f c hP hQ s).choose_spec x
  let g : U → V × J := fun x => (⟨F x.val, x.property⟩, j x)
  let k : V × J → U := fun y => ⟨((q y.2).symm y.1).val, by
    change F ((q y.2).symm y.1).val ∈ V
    rw [← hq, Homeomorph.apply_symm_apply]
    exact y.1.property⟩
  have hleft : Function.LeftInverse k g := by
    intro x
    apply Subtype.ext
    have he : q (j x) ⟨x.val, hj x⟩ = (⟨F x.val, x.property⟩ : V) :=
      Subtype.ext (hq _ _)
    change ((q (j x)).symm ⟨F x.val, x.property⟩).val = x.val
    rw [← he, Homeomorph.symm_apply_apply]
  have hright : Function.RightInverse k g := by
    intro y
    apply Prod.ext
    · apply Subtype.ext
      change F ((q y.2).symm y.1).val = y.1.val
      rw [← hq, Homeomorph.apply_symm_apply]
    · exact (hjuniq (k y) y.2 ((q y.2).symm y.1).property).symm
  have hjcont : Continuous j := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [((isOpen_orderOpenStarIntersection P (j x).val.finset).preimage
      continuous_subtype_val).mem_nhds (hj x)] with z hz
    exact (hjuniq z (j x) hz).symm
  have hg : Continuous g :=
    ((F.hom.continuous.comp continuous_subtype_val).subtype_mk _).prodMk hjcont
  have hk : Continuous k := by
    apply continuous_prod_of_discrete_right.mpr
    intro s
    exact ((q s).symm.continuous.subtype_val).subtype_mk _
  let e : U ≃ₜ V × J := {
    toFun := g
    invFun := k
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hg
    continuous_invFun := hk }
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro x
    exact orderOpenStarIntersection_positiveSupport_eq P c.finset.card hP
      (j x).val.finset (j x).property.1 x.val (hj x)
  · intro x p
    exact orderMap_full_star_coordinate_inverse f c.finset.card hP
      (j x).val.finset (j x).property.1 (orderFullStarSheet_injOn f c (j x)) x.val (hj x) p

end KIP126.Topology.SimplicialRealization
