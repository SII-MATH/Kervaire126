module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Iteration.Proofs
public import KIP126.Def.Topology.Simplex.Homotopy.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- For an actual simplex cone, the horn retraction is connected to the
identity by the actual affine cylinder homotopy, fixing its whole image. -/
theorem exists_orderCylinderHorn_strongDeformation (P V : Type u) [PartialOrder P]
    [Fintype V] (h : |nerve (WithTop P)| ≃ₜ stdSimplex ℝ V) :
    ∃ R : C(|nerve (WithTop P)| × I,|nerve (OrderCylinderHorn P)|),
      (∀ z, R (orderCylinderHornRealizationInclusion P z) = z) ∧
      (ContinuousMap.id _).HomotopicRel
        ((orderCylinderHornRealizationInclusion P).comp R)
        (Set.range (orderCylinderHornRealizationInclusion P)) := by
  obtain ⟨R,hR⟩ := exists_orderCylinderHorn_retraction_rightInverse P
  let e := h.prodCongr (Homeomorph.refl I)
  let ec : C(|nerve (WithTop P)| × I,stdSimplex ℝ V × I) := ⟨e,e.continuous⟩
  let ei : C(stdSimplex ℝ V × I,|nerve (WithTop P)| × I) := ⟨e.symm,e.symm.continuous⟩
  let F := (orderCylinderHornRealizationInclusion P).comp R
  have heq : Set.EqOn ec (ec.comp F) (Set.range (orderCylinderHornRealizationInclusion P)) := by
    rintro _ ⟨z,rfl⟩
    change e (orderCylinderHornRealizationInclusion P z) =
      e (orderCylinderHornRealizationInclusion P (R (orderCylinderHornRealizationInclusion P z)))
    rw [hR]
  have H := (KIP126.Topology.Simplex.cylinder_homotopicRel_of_eqOn ec (ec.comp F) _ heq).comp_continuousMap ei
  refine ⟨R,hR,?_⟩
  convert H using 1
  · apply ContinuousMap.ext
    intro x
    exact (e.symm_apply_apply x).symm
  · apply ContinuousMap.ext
    intro x
    exact (e.symm_apply_apply (F x)).symm

/-- The entire ordinary simplex boundary, after any finite number of
actual subdivisions, has the required strong cylinder deformation.
The simplex homeomorphism is supplied by the proved geometric construction. -/
theorem exists_iteratedOrderBoundaryCylinderHorn_strongDeformation
    (V : Type u) [LinearOrder V] [Fintype V] [Nontrivial V]
    [Fintype (orderProperChains V)] (n : ℕ) :
    ∃ R : C(|nerve (WithTop (iteratedOrderSubdivision (orderProperChains V) n))| × I,
        |nerve (OrderCylinderHorn (iteratedOrderSubdivision (orderProperChains V) n))|),
      (∀ z, R (orderCylinderHornRealizationInclusion
        (iteratedOrderSubdivision (orderProperChains V) n) z) = z) ∧
      (ContinuousMap.id _).HomotopicRel
        ((orderCylinderHornRealizationInclusion
          (iteratedOrderSubdivision (orderProperChains V) n)).comp R)
        (Set.range (orderCylinderHornRealizationInclusion
          (iteratedOrderSubdivision (orderProperChains V) n))) := by
  obtain ⟨h,_,_⟩ := exists_iteratedOrderBoundaryCone_stdSimplex_homeomorph V n
  exact exists_orderCylinderHorn_strongDeformation _ V h

end KIP126.Topology.SimplicialRealization
