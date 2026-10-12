module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Data
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open KIP126.StableHomotopy.Implementation
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The ordered cylinder's lower inclusion is exactly the lower
endpoint of the standard simplicial cylinder. -/
theorem orderCylinderIso_corner (P : Type u) [PartialOrder P] :
    orderCylinderHornCornerInclusion P ≫ (orderCylinderIso P).hom =
      realizationCylinderEnd (nerve P) 0 := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · exact CategoryTheory.Functor.ext (fun _ => rfl)
  · apply SSet.stdSimplex.objEquiv.injective
    rfl

theorem orderCylinderHomeomorph_corner (P : Type u) [PartialOrder P]
    (x : |nerve P|) :
    orderCylinderHomeomorph P (SSet.toTop.map (orderCylinderHornCornerInclusion P) x) =
      (x,0) := by
  change realizationCylinderHomeomorph (nerve P)
    (SSet.toTop.map (orderCylinderIso P).hom
      (SSet.toTop.map (orderCylinderHornCornerInclusion P) x)) = _
  rw [← TopCat.comp_app,← Functor.map_comp,orderCylinderIso_corner,
    realizationCylinderHomeomorph_end]
  rfl

theorem orderCylinderHornRealizationInclusion_bottom (P : Type u) [PartialOrder P]
    (x : |nerve (WithTop P)|) :
    orderCylinderHornRealizationInclusion P
      (SSet.toTop.map (orderCylinderHornBottomInclusion P) x) = (x,0) := by
  change orderCylinderHomeomorph (WithTop P)
    (SSet.toTop.map (orderCylinderHornInclusion P)
      (SSet.toTop.map (orderCylinderHornBottomInclusion P) x)) = _
  rw [← TopCat.comp_app,← Functor.map_comp]
  change orderCylinderHomeomorph (WithTop P)
    (SSet.toTop.map (orderCylinderHornCornerInclusion (WithTop P)) x) = _
  exact orderCylinderHomeomorph_corner (WithTop P) x

theorem orderCylinderHornRealizationInclusion_side (P : Type u) [PartialOrder P]
    (x : |nerve (OrderCylinder P)|) :
    orderCylinderHornRealizationInclusion P
      (SSet.toTop.map (orderCylinderHornSideInclusion P) x) =
      (SSet.toTop.map (orderMappingConeSourceTopInclusion P) (orderCylinderHomeomorph P x).1,
        (orderCylinderHomeomorph P x).2) := by
  have h : orderCylinderHornSideInclusion P ≫ orderCylinderHornInclusion P ≫
      (orderCylinderIso (WithTop P)).hom =
        (orderCylinderIso P).hom ≫ (orderMappingConeSourceTopInclusion P ▷ Δ[1]) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (fun _ => rfl)
    · apply SSet.stdSimplex.objEquiv.injective
      rfl
  change realizationCylinderHomeomorph (nerve (WithTop P))
    (SSet.toTop.map (orderCylinderIso (WithTop P)).hom
      (SSet.toTop.map (orderCylinderHornInclusion P)
        (SSet.toTop.map (orderCylinderHornSideInclusion P) x))) = _
  rw [← TopCat.comp_app,← Functor.map_comp,← TopCat.comp_app,← Functor.map_comp,
    h,Functor.map_comp,TopCat.comp_app,realizationCylinderHomeomorph_natural]
  rfl

/-- Choose homotopy extension into the actual horn itself. This keeps
the whole extension inside one displayed order-complex factor, instead
of asserting that an arbitrary extension into the target has such a factor. -/
theorem exists_orderCylinderHorn_retraction (P : Type u) [PartialOrder P] :
    ∃ R : C(|nerve (WithTop P)| × I,|nerve (OrderCylinderHorn P)|),
      (∀ x, R (x,0) = SSet.toTop.map (orderCylinderHornBottomInclusion P) x) ∧
      (∀ (x : |nerve P|) t,
        R (SSet.toTop.map (orderMappingConeSourceTopInclusion P) x,t) =
          SSet.toTop.map (orderCylinderHornSideInclusion P)
            ((orderCylinderHomeomorph P).symm (x,t))) := by
  let side : C(|nerve P| × I,|nerve (OrderCylinderHorn P)|) :=
    (SSet.toTop.map (orderCylinderHornSideInclusion P)).hom.comp
      ⟨(orderCylinderHomeomorph P).symm,(orderCylinderHomeomorph P).symm.continuous⟩
  apply realization_mono_hasHomotopyExtension (orderMappingConeSourceTopInclusion P)
    (SSet.toTop.obj (nerve (OrderCylinderHorn P)))
    (SSet.toTop.map (orderCylinderHornBottomInclusion P)).hom side
  intro x
  have he : (orderCylinderHomeomorph P).symm (x,0) =
      SSet.toTop.map (orderCylinderHornCornerInclusion P) x :=
    (orderCylinderHomeomorph P).symm_apply_eq.mpr (orderCylinderHomeomorph_corner P x).symm
  change SSet.toTop.map (orderCylinderHornSideInclusion P)
    ((orderCylinderHomeomorph P).symm (x,0)) = _
  rw [he,← TopCat.comp_app,← Functor.map_comp,← orderCylinderHorn_square,
    Functor.map_comp,TopCat.comp_app]

/-- Prescribed simplicial bottom and side maps extend through one
actual finite order complex whenever the underlying order is finite.
Both restrictions remain exact, including every side parameter. -/
theorem exists_orderCylinderHorn_factored_extension (P : Type u) [PartialOrder P]
    (Z : SSet.{u}) (f : nerve (WithTop P) ⟶ Z) (g : nerve (OrderCylinder P) ⟶ Z)
    (h : orderMappingConeSourceTopInclusion P ≫ f =
      orderCylinderHornCornerInclusion P ≫ g) :
    ∃ ψ : nerve (OrderCylinderHorn P) ⟶ Z,
      ∃ R : C(|nerve (WithTop P)| × I,|nerve (OrderCylinderHorn P)|),
        (∀ x, SSet.toTop.map ψ (R (x,0)) = SSet.toTop.map f x) ∧
        (∀ (x : |nerve P|) t,
          SSet.toTop.map ψ (R (SSet.toTop.map (orderMappingConeSourceTopInclusion P) x,t)) =
            SSet.toTop.map g ((orderCylinderHomeomorph P).symm (x,t))) := by
  let hp := orderCylinderHorn_isPushout P
  let ψ := hp.desc f g h
  obtain ⟨R,hR0,hRs⟩ := exists_orderCylinderHorn_retraction P
  refine ⟨ψ,R,?_,?_⟩
  · intro x
    rw [hR0,← TopCat.comp_app,← Functor.map_comp]
    change SSet.toTop.map (orderCylinderHornBottomInclusion P ≫ hp.desc f g h) x = _
    rw [hp.inl_desc]
  · intro x t
    rw [hRs,← TopCat.comp_app,← Functor.map_comp]
    change SSet.toTop.map (orderCylinderHornSideInclusion P ≫ hp.desc f g h) _ = _
    rw [hp.inr_desc]

/-- The chosen extension into the displayed horn is an actual
retraction of the entire bottom-side realization. -/
theorem exists_orderCylinderHorn_retraction_rightInverse (P : Type u) [PartialOrder P] :
    ∃ R : C(|nerve (WithTop P)| × I,|nerve (OrderCylinderHorn P)|),
      ∀ z, R (orderCylinderHornRealizationInclusion P z) = z := by
  obtain ⟨R,hR0,hRs⟩ := exists_orderCylinderHorn_retraction P
  refine ⟨R,?_⟩
  have h : TopCat.ofHom (Y := SSet.toTop.obj (nerve (OrderCylinderHorn P)))
      (R.comp (orderCylinderHornRealizationInclusion P)) =
        𝟙 (SSet.toTop.obj (nerve (OrderCylinderHorn P))) := by
    apply (orderCylinderHorn_realization_isPushout P).hom_ext
    · apply ConcreteCategory.hom_ext
      intro x
      change R (orderCylinderHornRealizationInclusion P
        (SSet.toTop.map (orderCylinderHornBottomInclusion P) x)) = _
      rw [orderCylinderHornRealizationInclusion_bottom,hR0]
      rfl
    · apply ConcreteCategory.hom_ext
      intro x
      change R (orderCylinderHornRealizationInclusion P
        (SSet.toTop.map (orderCylinderHornSideInclusion P) x)) = _
      rw [orderCylinderHornRealizationInclusion_side,hRs,Homeomorph.symm_apply_apply]
      rfl
  exact fun z => ConcreteCategory.congr_hom h z

end KIP126.Topology.SimplicialRealization
