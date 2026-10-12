module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Attachment.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual order mapping cone receives the continuous cone attachment
of every attaching map homotopic to its order map. The map is strictly
the target inclusion on the old space, and the cone map is changed only
by a genuine continuous homotopy. -/
theorem exists_orderMappingCone_continuous_attachment_map
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q)
    (a : SSet.toTop.obj (nerve P) ⟶ SSet.toTop.obj (nerve Q))
    {T : TopCat.{u}} (u : SSet.toTop.obj (nerve Q) ⟶ T)
    (v : SSet.toTop.obj (nerve (WithTop P)) ⟶ T)
    (hp : IsPushout a (SSet.toTop.map (orderMappingConeSourceTopInclusion P)) u v)
    (ha : a.hom.Homotopic (SSet.toTop.map (nerveMap f.monotone.functor)).hom) :
    ∃ r : T ⟶ SSet.toTop.obj (nerve (OrderMappingCone f)),
      u ≫ r = SSet.toTop.map
        (orderMappingCylinderTargetInclusion f ≫ orderMappingConeCylinderInclusion f) ∧
      (SSet.toTop.map (orderMappingConeTopInclusion f)).hom.Homotopic (v ≫ r).hom := by
  let b := orderMappingConeSourceTopInclusion P
  let c := orderMappingConeCylinderInclusion f
  let d := orderMappingConeTopInclusion f
  let q := orderMappingCylinderTargetInclusion f ≫ c
  obtain ⟨Hc⟩ := orderMappingCylinder_strongDeformation f
  have h₀ : ((SSet.toTop.map d).hom.comp (SSet.toTop.map b).hom).Homotopic
      ((SSet.toTop.map q).hom.comp (SSet.toTop.map (nerveMap f.monotone.functor)).hom) := by
    have hh := (ContinuousMap.Homotopy.refl (SSet.toTop.map c).hom).comp
      (Hc.toHomotopy.compContinuousMap (SSet.toTop.map (orderMappingCylinderSourceInclusion f)).hom)
    have hl : (SSet.toTop.map c).hom.comp
        ((ContinuousMap.id _).comp (SSet.toTop.map (orderMappingCylinderSourceInclusion f)).hom) =
        (SSet.toTop.map d).hom.comp (SSet.toTop.map b).hom := by
      change (SSet.toTop.map (orderMappingCylinderSourceInclusion f) ≫ SSet.toTop.map c).hom =
        (SSet.toTop.map b ≫ SSet.toTop.map d).hom
      rw [← Functor.map_comp,← Functor.map_comp]
      exact congrArg (fun k => (SSet.toTop.map k).hom) (orderMappingCone_square f)
    have hr : (SSet.toTop.map c).hom.comp
        (((SSet.toTop.map (orderMappingCylinderTargetInclusion f)).hom.comp
          (SSet.toTop.map (orderMappingCylinderProjection f)).hom).comp
            (SSet.toTop.map (orderMappingCylinderSourceInclusion f)).hom) =
        (SSet.toTop.map q).hom.comp (SSet.toTop.map (nerveMap f.monotone.functor)).hom := by
      change ((((SSet.toTop.map (orderMappingCylinderSourceInclusion f) ≫
        SSet.toTop.map (orderMappingCylinderProjection f)) ≫
          SSet.toTop.map (orderMappingCylinderTargetInclusion f)) ≫ SSet.toTop.map c)).hom =
        (SSet.toTop.map (nerveMap f.monotone.functor) ≫ SSet.toTop.map q).hom
      simp only [← Functor.map_comp,orderMappingCylinder_source_projection,Category.assoc,q]
    exact ⟨hh.cast hl hr⟩
  have h : ((SSet.toTop.map d).hom.comp (SSet.toTop.map b).hom).Homotopic
      ((SSet.toTop.map q).hom.comp a.hom) :=
    h₀.trans ((ContinuousMap.Homotopic.refl (SSet.toTop.map q).hom).comp ha.symm)
  obtain ⟨H⟩ := h
  obtain ⟨r,hr,H',_⟩ := exists_map_of_realized_mono_attachment_with_homotopy
    b a u v hp (SSet.toTop.map q) (SSet.toTop.map d) H
  exact ⟨r,hr,⟨H'⟩⟩

end KIP126.Topology.SimplicialRealization
