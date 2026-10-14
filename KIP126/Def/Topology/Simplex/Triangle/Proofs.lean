module

public import KIP126.Def.Topology.Simplex.Triangle.Data

@[expose] public section

namespace KIP126.Topology.Simplex

open CategoryTheory
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

theorem triangleEdge_apply (i j : Fin 3) (t : I) :
    triangleEdge i t j =
      (if (SimplexCategory.δ i).toOrderHom 0 = j then 1 - (t : ℝ) else 0) +
      (if (SimplexCategory.δ i).toOrderHom 1 = j then (t : ℝ) else 0) := by
  change FunOnFinite.linearMap ℝ ℝ (SimplexCategory.δ i).toOrderHom
    (stdSimplexHomeomorphUnitInterval.symm t) j = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  change (∑ a : Fin 2, if (SimplexCategory.δ i).toOrderHom a = j then
    (stdSimplexHomeomorphUnitInterval.symm t) a else 0) = _
  rw [Fin.sum_univ_two]
  rfl

@[simp] theorem triangleEdge_zero (i : Fin 3) :
    triangleEdge i 0 = stdSimplex.vertex ((SimplexCategory.δ i).toOrderHom 0) := by
  change stdSimplex.map (SimplexCategory.δ i).toOrderHom
    (stdSimplexHomeomorphUnitInterval.symm 0) = _
  rw [show stdSimplexHomeomorphUnitInterval.symm 0 = stdSimplex.vertex 0 from
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr rfl,stdSimplex.map_vertex]

@[simp] theorem triangleEdge_one (i : Fin 3) :
    triangleEdge i 1 = stdSimplex.vertex ((SimplexCategory.δ i).toOrderHom 1) := by
  change stdSimplex.map (SimplexCategory.δ i).toOrderHom
    (stdSimplexHomeomorphUnitInterval.symm 1) = _
  rw [show stdSimplexHomeomorphUnitInterval.symm 1 = stdSimplex.vertex 1 from
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr rfl,stdSimplex.map_vertex]

@[simp] theorem triangleTime_edge_two (t : I) :
    (triangleTime (triangleEdge 2 t) : ℝ) = (t : ℝ) / 2 := by
  change triangleEdge 2 t 1 / 2 + triangleEdge 2 t 2 = _
  simp +decide [triangleEdge_apply]

@[simp] theorem triangleTime_edge_zero (t : I) :
    (triangleTime (triangleEdge 0 t) : ℝ) = ((t : ℝ) + 1) / 2 := by
  change triangleEdge 0 t 1 / 2 + triangleEdge 0 t 2 = _
  simp +decide [triangleEdge_apply]
  ring

@[simp] theorem triangleTime_edge_one (t : I) :
    triangleTime (triangleEdge 1 t) = t := by
  apply Subtype.ext
  change triangleEdge 1 t 1 / 2 + triangleEdge 1 t 2 = _
  simp +decide [triangleEdge_apply]

/-- Two actual simplex-valued paths with the same endpoints admit a
continuous homotopy fixed at both endpoints, by the affine formula. -/
theorem simplex_paths_homotopic {V : Type*} [Fintype V]
    {a b : stdSimplex ℝ V} (p q : Path a b) : p.Homotopic q := by
  obtain ⟨H,hH⟩ := exists_affine_homotopy p.toContinuousMap q.toContinuousMap
  refine ⟨⟨H,?_⟩⟩
  intro t s hs
  rcases hs with rfl | hs
  · apply stdSimplex.ext
    funext j
    change H (t,0) j = p 0 j
    rw [hH]
    change (1 - (t : ℝ)) * p 0 j + (t : ℝ) * q 0 j = p 0 j
    rw [p.source,q.source]
    ring
  · have hs : s = 1 := hs
    subst s
    apply stdSimplex.ext
    funext j
    change H (t,1) j = p 1 j
    rw [hH]
    change (1 - (t : ℝ)) * p 1 j + (t : ℝ) * q 1 j = p 1 j
    rw [p.target,q.target]
    ring

end KIP126.Topology.Simplex
