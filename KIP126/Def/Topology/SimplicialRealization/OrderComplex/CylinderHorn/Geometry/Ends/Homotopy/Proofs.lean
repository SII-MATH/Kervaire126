module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Ends.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Restrict a horn-relative two-parameter homotopy to either end. The
result fixes the entire boundary of that end, with the restriction
formula retained pointwise. -/
theorem orderCylinder_homotopyRel_end (P : Type u) [PartialOrder P]
    {Y : Type v} [TopologicalSpace Y]
    {f g : C(|nerve (OrderCylinder (WithTop P))|,Y)}
    (H : f.HomotopyRel g (Set.range (SSet.toTop.map (orderCylinderHornInclusion P))))
    (i : Fin 2) :
    ∃ H' : (f.comp (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) i)).hom).HomotopyRel
      (g.comp (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) i)).hom)
      (Set.range (SSet.toTop.map (orderMappingConeSourceTopInclusion P))),
      ∀ (t : I) x, H' (t,x) = H (t,SSet.toTop.map (orderCylinderEndInclusion (WithTop P) i) x) := by
  refine ⟨{
    toFun := fun z => H (z.1,SSet.toTop.map (orderCylinderEndInclusion (WithTop P) i) z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      ((SSet.toTop.map (orderCylinderEndInclusion (WithTop P) i)).hom.continuous.comp continuous_snd))
    map_zero_left := fun x => H.apply_zero _
    map_one_left := fun x => H.apply_one _
    prop' := ?_ },fun _ _ => rfl⟩
  rintro t _ ⟨x,rfl⟩
  apply H.eq_fst
  refine ⟨SSet.toTop.map (orderCylinderHornSideInclusion P)
    (SSet.toTop.map (orderCylinderEndInclusion P i) x),?_⟩
  rw [← TopCat.comp_app,← Functor.map_comp,← TopCat.comp_app,← Functor.map_comp]
  rw [← orderCylinderHorn_end_square,Functor.map_comp,TopCat.comp_app]

end KIP126.Topology.SimplicialRealization
