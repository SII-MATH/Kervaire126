module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Concatenation.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Comparison.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual canonical side homotopy on an order cone extends through
the displayed horn order complex. This extension retains every value
on the bottom and side, and its finite order factor is constructed. -/
theorem singularHomotopyLift_extend_orderCone
    (P : Type u) [PartialOrder P] (B : TopCat.{u})
    (f : nerve (WithTop P) ⟶ TopCat.toSSet.obj B) (b : C(|nerve P|,B))
    (H : ((sSetTopAdj.counit.app B).hom.comp
      (SSet.toTop.map (orderMappingConeSourceTopInclusion P ≫ f)).hom).Homotopy b) :
    ∃ ψ : nerve (OrderCylinderHorn P) ⟶ TopCat.toSSet.obj B,
      ∃ R : C(|nerve (WithTop P)| × I,|nerve (OrderCylinderHorn P)|),
        (∀ x, SSet.toTop.map ψ (R (x,0)) = SSet.toTop.map f x) ∧
        (∀ (x : |nerve P|) t,
          SSet.toTop.map ψ (R (SSet.toTop.map (orderMappingConeSourceTopInclusion P) x,t)) =
            singularHomotopyLift (nerve P) B H (t,x)) := by
  let h : C(|nerve P| × I,B) := H.toContinuousMap.comp ContinuousMap.prodSwap
  let g : nerve (OrderCylinder P) ⟶ TopCat.toSSet.obj B :=
    (orderCylinderIso P).hom ≫ singularCylinderAdjoint (nerve P) B h
  have hg (z : |nerve (OrderCylinder P)|) :
      SSet.toTop.map g z = singularCylinder (nerve P) B h (orderCylinderHomeomorph P z) := by
    change SSet.toTop.map ((orderCylinderIso P).hom ≫ singularCylinderAdjoint (nerve P) B h) z =
      SSet.toTop.map (singularCylinderAdjoint (nerve P) B h)
        ((realizationCylinderHomeomorph (nerve P)).symm
          (realizationCylinderHomeomorph (nerve P)
            (SSet.toTop.map (orderCylinderIso P).hom z)))
    rw [Functor.map_comp,TopCat.comp_app,Homeomorph.symm_apply_apply]
  have he : orderMappingConeSourceTopInclusion P ≫ f =
      orderCylinderHornCornerInclusion P ≫ g := by
    apply (sSetTopAdj.homEquiv (nerve P) B).symm.injective
    rw [Adjunction.homEquiv_counit,Adjunction.homEquiv_counit]
    apply ConcreteCategory.hom_ext
    intro x
    change sSetTopAdj.counit.app B (SSet.toTop.map (orderMappingConeSourceTopInclusion P ≫ f) x) =
      sSetTopAdj.counit.app B (SSet.toTop.map (orderCylinderHornCornerInclusion P ≫ g) x)
    rw [SSet.toTop.map_comp (orderCylinderHornCornerInclusion P) g,TopCat.comp_app,
      hg,orderCylinderHomeomorph_corner,singularCylinder_evaluation]
    exact (H.apply_zero x).symm
  obtain ⟨ψ,R,hR0,hRs⟩ := exists_orderCylinderHorn_factored_extension P
    (TopCat.toSSet.obj B) f g he
  refine ⟨ψ,R,hR0,?_⟩
  intro x t
  rw [hRs,hg,Homeomorph.apply_symm_apply]
  rfl

end KIP126.StableHomotopy.Implementation
