module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.FiniteOrder.Coherence.Factored.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Ends.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The upper face changes by a homotopy fixing its entire boundary,
and that complete homotopy factors through one actual order cylinder.
This records the precise change allowed by horn-relative correction. -/
theorem exists_singularOrderCylinderHorn_top_factored_homotopy
    (P V : Type u) [PartialOrder P] [Fintype V]
    (h : |nerve (WithTop P)| ≃ₜ stdSimplex ℝ V) (B : TopCat.{u})
    (ψ : nerve (OrderCylinderHorn P) ⟶ TopCat.toSSet.obj B) :
    ∃ r : C(|nerve (OrderCylinder (WithTop P))|,|nerve (OrderCylinderHorn P)|),
      ∃ a : nerve (OrderCylinder (WithTop P)) ⟶ TopCat.toSSet.obj B,
        orderCylinderHornInclusion P ≫ a = ψ ∧
        ∃ H : (((SSet.toTop.map ψ).hom.comp r).comp
          (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1)).hom).HomotopyRel
            (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1 ≫ a)).hom
            (Set.range (SSet.toTop.map (orderMappingConeSourceTopInclusion P))),
          ∃ J : C(I × |nerve (WithTop P)|,|nerve (OrderCylinder (WithTop P))|),
            ∀ z, H z = SSet.toTop.map a (J z) := by
  obtain ⟨r,a,ha,_,H,J,hJ⟩ := exists_singularOrderCylinderHorn_canonical_factored_homotopy P V h B ψ
  obtain ⟨HT,hT⟩ := orderCylinder_homotopyRel_end P H 1
  have he : (SSet.toTop.map a).hom.comp
      (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1)).hom =
      (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1 ≫ a)).hom := by
    rw [Functor.map_comp]
    rfl
  let J' := J.comp ((ContinuousMap.id I).prodMap
    (SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1)).hom)
  refine ⟨r,a,ha,HT.cast rfl he,J',?_⟩
  intro z
  change HT z = SSet.toTop.map a (J (z.1,SSet.toTop.map (orderCylinderEndInclusion (WithTop P) 1) z.2))
  exact (hT z.1 z.2).trans (hJ _)

end KIP126.StableHomotopy.Implementation
