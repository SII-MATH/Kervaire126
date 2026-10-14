module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Proofs

@[expose] public section

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- Either actual endpoint of the ordered cylinder. -/
def orderCylinderEndEmbedding (P : Type u) [PartialOrder P] (i : Fin 2) :
    P ↪o OrderCylinder P where
  toFun p := (p,i)
  inj' := by intro p q h; exact congrArg Prod.fst h
  map_rel_iff' := by intro p q; change (p ≤ q ∧ i ≤ i) ↔ p ≤ q; simp

def orderCylinderEndInclusion (P : Type u) [PartialOrder P] (i : Fin 2) :
    nerve P ⟶ nerve (OrderCylinder P) :=
  nerveMap (orderCylinderEndEmbedding P i).monotone.functor

end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial MonoidalCategory
open KIP126.StableHomotopy.Implementation
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

theorem orderCylinderIso_end (P : Type u) [PartialOrder P] (i : Fin 2) :
    orderCylinderEndInclusion P i ≫ (orderCylinderIso P).hom =
      realizationCylinderEnd (nerve P) i := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · exact CategoryTheory.Functor.ext (fun _ => rfl)
  · apply SSet.stdSimplex.objEquiv.injective
    rfl

theorem orderCylinderHomeomorph_end (P : Type u) [PartialOrder P]
    (i : Fin 2) (x : |nerve P|) :
    orderCylinderHomeomorph P (SSet.toTop.map (orderCylinderEndInclusion P i) x) =
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) := by
  change realizationCylinderHomeomorph (nerve P)
    (SSet.toTop.map (orderCylinderIso P).hom
      (SSet.toTop.map (orderCylinderEndInclusion P i) x)) = _
  rw [← TopCat.comp_app,← Functor.map_comp,orderCylinderIso_end,
    realizationCylinderHomeomorph_end]

/-- Every endpoint of the entire side boundary lies in the actual horn,
including the boundary of the free upper face. -/
theorem orderCylinderHorn_end_square (P : Type u) [PartialOrder P] (i : Fin 2) :
    orderMappingConeSourceTopInclusion P ≫ orderCylinderEndInclusion (WithTop P) i =
      orderCylinderEndInclusion P i ≫ orderCylinderHornSideInclusion P ≫
        orderCylinderHornInclusion P := rfl

end KIP126.Topology.SimplicialRealization

end
