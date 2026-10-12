module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

theorem orderCylinderHorn_square (P : Type u) [PartialOrder P] :
    orderMappingConeSourceTopInclusion P ≫ orderCylinderHornBottomInclusion P =
      orderCylinderHornCornerInclusion P ≫ orderCylinderHornSideInclusion P := rfl

instance orderCylinderHornBottomInclusion_mono (P : Type u) [PartialOrder P] :
    Mono (orderCylinderHornBottomInclusion P) :=
  nerveMap_mono_of_injective_orderHom (orderCylinderHornBottomEmbedding P).toOrderHom
    (orderCylinderHornBottomEmbedding P).injective

instance orderCylinderHornSideInclusion_mono (P : Type u) [PartialOrder P] :
    Mono (orderCylinderHornSideInclusion P) :=
  nerveMap_mono_of_injective_orderHom (orderCylinderHornSideEmbedding P).toOrderHom
    (orderCylinderHornSideEmbedding P).injective

instance orderCylinderHornCornerInclusion_mono (P : Type u) [PartialOrder P] :
    Mono (orderCylinderHornCornerInclusion P) :=
  nerveMap_mono_of_injective_orderHom (orderCylinderHornCornerEmbedding P).toOrderHom
    (orderCylinderHornCornerEmbedding P).injective

/-- Each actual simplex of the horn lies in the bottom or in the side.
The condition on its last vertex forces the same condition on all vertices. -/
theorem orderCylinderHorn_simplex_cover (P : Type u) [PartialOrder P]
    (d : SimplexCategoryᵒᵖ) (s : (nerve (OrderCylinderHorn P)).obj d) :
    s ∈ Set.range ((orderCylinderHornBottomInclusion P).app d) ∨
      s ∈ Set.range ((orderCylinderHornSideInclusion P).app d) := by
  rcases (s.obj (Fin.last d.unop.len)).property with hb | hs
  · left
    apply (nerveMap_orderEmbedding_range_iff (orderCylinderHornBottomEmbedding P) d s).mpr
    intro k
    have hk := (s.monotone (Fin.le_last k)).2
    change (s.obj k).val.2 ≤ (s.obj (Fin.last d.unop.len)).val.2 at hk
    have hzero : (s.obj k).val.2 = 0 :=
      le_antisymm (by simpa only [hb] using hk) (Fin.zero_le _)
    refine ⟨(s.obj k).val.1,?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hzero.symm
  · right
    apply (nerveMap_orderEmbedding_range_iff (orderCylinderHornSideEmbedding P) d s).mpr
    intro k
    have hk := (s.monotone (Fin.le_last k)).1
    change (s.obj k).val.1 ≤ (s.obj (Fin.last d.unop.len)).val.1 at hk
    have hn : (s.obj k).val.1 ≠ ⊤ := by
      intro he
      rw [he] at hk
      exact hs (top_le_iff.mp hk)
    obtain ⟨p,hp⟩ := WithTop.ne_top_iff_exists.mp hn
    refine ⟨(p,(s.obj k).val.2),?_⟩
    apply Subtype.ext
    exact Prod.ext hp rfl

/-- The bottom and side intersect exactly in their common lower base. -/
theorem orderCylinderHorn_simplex_intersection (P : Type u) [PartialOrder P]
    (d : SimplexCategoryᵒᵖ) (s : (nerve (WithTop P)).obj d)
    (t : (nerve (OrderCylinder P)).obj d)
    (h : (orderCylinderHornBottomInclusion P).app d s =
      (orderCylinderHornSideInclusion P).app d t) :
    ∃ a : (nerve P).obj d,
      (orderMappingConeSourceTopInclusion P).app d a = s ∧
      (orderCylinderHornCornerInclusion P).app d a = t := by
  have hs : s ∈ Set.range ((orderMappingConeSourceTopInclusion P).app d) := by
    apply (nerveMap_orderEmbedding_range_iff (orderMappingConeSourceTopEmbedding P) d s).mpr
    intro k
    have hk := congrArg (fun z : (nerve (OrderCylinderHorn P)).obj d => (z.obj k).val.1) h
    exact ⟨(t.obj k).1,hk.symm⟩
  obtain ⟨a,ha⟩ := hs
  refine ⟨a,ha,?_⟩
  apply (CategoryTheory.mono_iff_injective ((orderCylinderHornSideInclusion P).app d)).mp
    (inferInstance : Mono ((orderCylinderHornSideInclusion P).app d))
  change (orderCylinderHornBottomInclusion P).app d
    ((orderMappingConeSourceTopInclusion P).app d a) = _
  rw [ha]
  exact h

/-- The cone-cylinder horn is a genuine simplicial pushout, without
any approximation or cofibrancy assumption. -/
theorem orderCylinderHorn_isPushout (P : Type u) [PartialOrder P] :
    IsPushout (orderMappingConeSourceTopInclusion P) (orderCylinderHornCornerInclusion P)
      (orderCylinderHornBottomInclusion P) (orderCylinderHornSideInclusion P) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply Types.isPushout_of_isPullback_of_mono'
  · apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_,?_,orderCylinderHorn_simplex_intersection P d⟩
    · exact congrArg (fun z => z.app d) (orderCylinderHorn_square P)
    · intro x y h
      exact (CategoryTheory.mono_iff_injective
        ((orderMappingConeSourceTopInclusion P).app d)).mp inferInstance h.1
  · apply Set.eq_univ_of_forall
    exact orderCylinderHorn_simplex_cover P d
  · intro x y _ _ h
    exact (CategoryTheory.mono_iff_injective
      ((orderCylinderHornSideInclusion P).app d)).mp inferInstance h

theorem orderCylinderHorn_realization_isPushout (P : Type u) [PartialOrder P] :
    IsPushout (SSet.toTop.map (orderMappingConeSourceTopInclusion P))
      (SSet.toTop.map (orderCylinderHornCornerInclusion P))
      (SSet.toTop.map (orderCylinderHornBottomInclusion P))
      (SSet.toTop.map (orderCylinderHornSideInclusion P)) :=
  (orderCylinderHorn_isPushout P).map SSet.toTop

instance orderCylinderHorn_nerve_finite (P : Type u) [PartialOrder P] [Finite P] :
    (nerve (OrderCylinderHorn P)).Finite :=
  finite_nerve_of_finite_order (OrderCylinderHorn P)

end KIP126.Topology.SimplicialRealization
