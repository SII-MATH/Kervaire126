module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Deformation.Proofs
public import KIP126.Def.Topology.Homotopy.Precomposition.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Express the strong horn deformation on the actual nerve realization,
retaining the realized simplicial inclusion and its strict retraction. -/
theorem exists_orderCylinderHorn_realization_strongDeformation
    (P V : Type u) [PartialOrder P] [Fintype V]
    (h : |nerve (WithTop P)| ≃ₜ stdSimplex ℝ V) :
    ∃ r : C(|nerve (OrderCylinder (WithTop P))|,|nerve (OrderCylinderHorn P)|),
      (∀ z, r (SSet.toTop.map (orderCylinderHornInclusion P) z) = z) ∧
      ((SSet.toTop.map (orderCylinderHornInclusion P)).hom.comp r).HomotopicRel
        (ContinuousMap.id _) (Set.range (SSet.toTop.map (orderCylinderHornInclusion P))) := by
  obtain ⟨R,hR,H⟩ := exists_orderCylinderHorn_strongDeformation P V h
  let e := orderCylinderHomeomorph (WithTop P)
  let ec : C(|nerve (OrderCylinder (WithTop P))|,|nerve (WithTop P)| × I) := ⟨e,e.continuous⟩
  let ei : C(|nerve (WithTop P)| × I,|nerve (OrderCylinder (WithTop P))|) :=
    ⟨e.symm,e.symm.continuous⟩
  let r := R.comp ec
  refine ⟨r,fun z => hR z,?_⟩
  have hpre := homotopicRel_precomp H ec
    (T := Set.range (SSet.toTop.map (orderCylinderHornInclusion P))) (by
      rintro _ ⟨z,rfl⟩
      exact ⟨z,rfl⟩)
  have hD := hpre.comp_continuousMap ei
  apply ContinuousMap.HomotopicRel.symm
  convert hD using 1
  · ext x
    exact (e.symm_apply_apply x).symm
  · ext x
    exact (e.symm_apply_apply (SSet.toTop.map (orderCylinderHornInclusion P) (r x))).symm

end KIP126.Topology.SimplicialRealization
