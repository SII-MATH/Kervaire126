module

public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Barycentric.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- After a map collapses the simplex boundary, geometric subdivision
and the actual last-vertex comparison are homotopic relative to the
entire subdivided boundary. Face preservation supplies the relative
condition, including all boundary points rather than only vertices. -/
theorem simplexSubdivisionBarycentric_postcomp_homotopicRel_boundary
    (n : SimplexCategory) {Y : Type v} [TopologicalSpace Y]
    (f : C(stdSimplex ℝ (Fin (n.len+1)),Y)) (y₀ : Y)
    (hf : ∀ y, (∃ j, y j = 0) → f y = y₀) :
    (f.comp (simplexSubdivisionBarycentric.{u} n)).HomotopicRel
      (f.comp
        ((⟨SimplexCategory.toTopHomeo n,(SimplexCategory.toTopHomeo n).continuous⟩ :
          C(|SSet.stdSimplex.obj n|,stdSimplex ℝ (Fin (n.len+1)))).comp
            (SSet.toTop.map (simplexSubdivisionLastVertex n)).hom))
      {x | ∃ j, simplexSubdivisionBarycentric n x j = 0} := by
  obtain ⟨H,hH⟩ := exists_simplexSubdivisionBarycentric_face_homotopy.{u} n
  refine ⟨{
    toFun := fun z => f (H z)
    continuous_toFun := f.continuous.comp H.continuous
    map_zero_left := fun x => congrArg f (H.apply_zero x)
    map_one_left := fun x => congrArg f (H.apply_one x)
    prop' := ?_ }⟩
  intro t x hx
  obtain ⟨j,hj⟩ := hx
  exact (hf (H (t,x)) ⟨j,hH t x j hj⟩).trans
    (hf (simplexSubdivisionBarycentric n x) ⟨j,hj⟩).symm

end KIP126.Topology.SimplicialRealization
