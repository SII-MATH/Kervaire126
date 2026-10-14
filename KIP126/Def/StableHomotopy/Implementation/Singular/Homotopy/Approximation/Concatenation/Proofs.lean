module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Concatenation.Data
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Prism.Cylinder.Proofs
public import KIP126.Def.Topology.Simplex.Triangle.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial KIP126.Topology.Simplex
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

theorem singularHomotopyLift_evaluation (K : SSet.{u}) (B : TopCat.{u})
    {a b : C(|K|,B)} (H : a.Homotopy b) (z : I × |K|) :
    sSetTopAdj.counit.app B (singularHomotopyLift K B H z) = H z :=
  singularCylinder_evaluation K B _ (z.2,z.1)

private theorem trans_triangleEdge_two {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {a b c : C(X,Y)} (H : a.Homotopy b) (G : b.Homotopy c)
    (x : X) (t : I) :
    (H.trans G) (triangleTime (triangleEdge 2 t),x) = H (t,x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have he := triangleTime_edge_two t
  rw [dif_pos (by rw [he]; linarith [t.property.2])]
  apply congrArg H
  apply congrArg (fun s : I => (s,x))
  apply Subtype.ext
  change 2 * (triangleTime (triangleEdge 2 t) : ℝ) = (t : ℝ)
  rw [he]
  ring

private theorem trans_triangleEdge_zero {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {a b c : C(X,Y)} (H : a.Homotopy b) (G : b.Homotopy c)
    (x : X) (t : I) :
    (H.trans G) (triangleTime (triangleEdge 0 t),x) = G (t,x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  have he := triangleTime_edge_zero t
  split_ifs with h
  · have ht : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      rw [he] at h
      linarith [t.property.1]
    subst t
    have htime : (⟨2 * (triangleTime (triangleEdge 0 0) : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨(triangleTime (triangleEdge 0 0)).property.1,h⟩⟩ : I) = 1 := by
      apply Subtype.ext
      change 2 * (triangleTime (triangleEdge 0 0) : ℝ) = 1
      rw [triangleTime_edge_zero]
      norm_num
    rw [htime,H.apply_one,G.apply_zero]
  · apply congrArg G
    apply congrArg (fun s : I => (s,x))
    apply Subtype.ext
    change 2 * (triangleTime (triangleEdge 0 t) : ℝ) - 1 = (t : ℝ)
    rw [he]
    ring

/-- Lifting a concatenated homotopy is homotopic to concatenating its
two lifts, relative to both whole endpoint slices. The comparison is
the actual triangle prism, not an assumed compatibility of lifts. -/
theorem singularHomotopyLift_trans_homotopicRel (K : SSet.{u}) (B : TopCat.{u})
    {a b c : C(|K|,B)} (H : a.Homotopy b) (G : b.Homotopy c) :
    (singularHomotopyLift K B (H.trans G)).toContinuousMap.HomotopicRel
      ((singularHomotopyLift K B H).trans (singularHomotopyLift K B G)).toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1} := by
  let F : C(|K| × stdSimplex ℝ (Fin 3),B) :=
    (H.trans G).toContinuousMap.comp
      ((triangleTime.comp ContinuousMap.snd).prodMk ContinuousMap.fst)
  let L := singularPrism K B 2 F
  have hedge (i : Fin 3) (x : |K|) (t : I) :
      L (x,triangleEdge i t) = singularCylinder K B
        (F.comp ((ContinuousMap.id _).prodMap (triangleEdge i))) (x,t) := by
    change singularPrism K B 2 F (x,stdSimplex.map
      (SimplexCategory.δ i).toOrderHom (stdSimplexHomeomorphUnitInterval.symm t)) = _
    rw [singularPrism_simplex,singularPrism_one]
    rfl
  have htwo (x : |K|) (t : I) :
      L (x,triangleEdge 2 t) = singularHomotopyLift K B H (t,x) := by
    rw [hedge]
    have he : F.comp ((ContinuousMap.id _).prodMap (triangleEdge 2)) =
        H.toContinuousMap.comp ContinuousMap.prodSwap := by
      apply ContinuousMap.ext
      intro z
      exact trans_triangleEdge_two H G z.1 z.2
    rw [he]
    rfl
  have hzero (x : |K|) (t : I) :
      L (x,triangleEdge 0 t) = singularHomotopyLift K B G (t,x) := by
    rw [hedge]
    have he : F.comp ((ContinuousMap.id _).prodMap (triangleEdge 0)) =
        G.toContinuousMap.comp ContinuousMap.prodSwap := by
      apply ContinuousMap.ext
      intro z
      exact trans_triangleEdge_zero H G z.1 z.2
    rw [he]
    rfl
  have hone (x : |K|) (t : I) :
      L (x,triangleEdge 1 t) = singularHomotopyLift K B (H.trans G) (t,x) := by
    rw [hedge]
    have he : F.comp ((ContinuousMap.id _).prodMap (triangleEdge 1)) =
        (H.trans G).toContinuousMap.comp ContinuousMap.prodSwap := by
      apply ContinuousMap.ext
      intro z
      change (H.trans G) (triangleTime (triangleEdge 1 z.2),z.1) = _
      rw [triangleTime_edge_one]
      rfl
    rw [he]
    rfl
  let p : Path (stdSimplex.vertex (0 : Fin 3)) (stdSimplex.vertex 2) := {
    toContinuousMap := triangleEdge 1
    source' := triangleEdge_zero 1
    target' := triangleEdge_one 1 }
  let q₀ : Path (stdSimplex.vertex (0 : Fin 3)) (stdSimplex.vertex 1) := {
    toContinuousMap := triangleEdge 2
    source' := triangleEdge_zero 2
    target' := triangleEdge_one 2 }
  let q₁ : Path (stdSimplex.vertex (1 : Fin 3)) (stdSimplex.vertex 2) := {
    toContinuousMap := triangleEdge 0
    source' := triangleEdge_zero 0
    target' := triangleEdge_one 0 }
  obtain ⟨A⟩ := simplex_paths_homotopic p (q₀.trans q₁)
  refine ⟨{
    toFun := fun z => L (z.2.2,A (z.1,z.2.1))
    continuous_toFun := L.continuous.comp (continuous_snd.snd.prodMk
      (A.continuous.comp (continuous_fst.prodMk continuous_snd.fst)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    rw [A.apply_zero]
    exact hone z.2 z.1
  · rintro ⟨t,x⟩
    rw [A.apply_one]
    change L (x,(q₀.trans q₁) t) =
      ((singularHomotopyLift K B H).trans (singularHomotopyLift K B G)) (t,x)
    rw [Path.trans_apply,ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> [exact htwo x _; exact hzero x _]
  · intro t z hz
    change L (z.2,A (t,z.1)) = singularHomotopyLift K B (H.trans G) z
    rw [A.eq_fst t hz]
    exact hone z.2 z.1

end KIP126.StableHomotopy.Implementation
