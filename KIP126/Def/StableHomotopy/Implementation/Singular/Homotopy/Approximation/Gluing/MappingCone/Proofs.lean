module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Gluing.Disjoint.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Ends.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits Simplicial
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- An evaluated homotopy between the attaching map and an actual
singular cone boundary gives an actual simplicial singular map on the
finite-order mapping cone, retaining both the old target and new cone
strictly. The cylinder changes by a homotopy fixing its entire target. -/
theorem singularMap_glue_orderMappingCone {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (B : TopCat.{u}) (g : nerve Q ⟶ TopCat.toSSet.obj B)
    (d : nerve (WithTop P) ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom).comp
        (SSet.toTop.map (nerveMap f.monotone.functor)).hom).Homotopic
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map d).hom).comp
        (SSet.toTop.map (orderMappingConeSourceTopInclusion P)).hom)) :
    ∃ k : nerve (OrderMappingCone f) ⟶ TopCat.toSSet.obj B,
      orderMappingConeTopInclusion f ≫ k = d ∧
      orderMappingCylinderTargetInclusion f ≫ orderMappingConeCylinderInclusion f ≫ k = g ∧
      (SSet.toTop.map (orderMappingCylinderProjection f ≫ g)).hom.HomotopicRel
        (SSet.toTop.map (orderMappingConeCylinderInclusion f ≫ k)).hom
        (Set.range (SSet.toTop.map (orderMappingCylinderTargetInclusion f))) := by
  letI : Mono (simplicialSumDesc (orderMappingCylinderSourceInclusion f)
      (orderMappingCylinderTargetInclusion f)) := orderMappingCylinderEndsInclusion_mono f
  have h' : (((sSetTopAdj.counit.app B).hom.comp
      (SSet.toTop.map (orderMappingCylinderProjection f ≫ g)).hom).comp
        (SSet.toTop.map (orderMappingCylinderSourceInclusion f)).hom).Homotopic
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map d).hom).comp
        (SSet.toTop.map (orderMappingConeSourceTopInclusion P)).hom) := by
    convert h using 1
    change ((SSet.toTop.map (orderMappingCylinderSourceInclusion f) ≫
      SSet.toTop.map (orderMappingCylinderProjection f ≫ g)) ≫ sSetTopAdj.counit.app B).hom =
      (((SSet.toTop.map (nerveMap f.monotone.functor) ≫ SSet.toTop.map g) ≫
        sSetTopAdj.counit.app B)).hom
    simp only [← Functor.map_comp,← Category.assoc,orderMappingCylinder_source_projection]
  obtain ⟨k,hk,ht,H⟩ := singularMap_glue_along_homotopy_fixing_disjoint
    (orderMappingCone_isPushout f) (orderMappingCylinderTargetInclusion f) B
    (orderMappingCylinderProjection f ≫ g) d h'
  refine ⟨k,hk,?_,H⟩
  simpa only [← Category.assoc,orderMappingCylinder_target_projection,Category.id_comp] using ht

end KIP126.StableHomotopy.Implementation
