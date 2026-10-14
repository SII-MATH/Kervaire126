module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

/-! Low-dimensional smooth maps miss a point of a unit sphere.
The proof uses a stereographic chart and the Hausdorff-dimension estimate
for locally Lipschitz maps, rather than assuming sphere connectivity. -/

namespace KIP126.Topology.Sphere

open Metric Module Submodule MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- If a smooth map has domain dimension less than the sphere dimension,
its spherical values omit a point different from any specified basepoint.
The set `s` need not be open, compact, or convex. -/
theorem exists_sphere_point_outside_image {n : ℕ} [Fact (finrank ℝ F = n + 1)]
    (f : E → F) (hf : ContDiff ℝ 1 f) (s : Set E)
    (hs : ∀ x ∈ s, ‖f x‖ = 1) (hdim : finrank ℝ E < n)
    (b : Metric.sphere (0 : F) 1) :
    ∃ y : Metric.sphere (0 : F) 1, b ≠ y ∧ ∀ x ∈ s, f x ≠ (y : F) := by
  letI : FiniteDimensional ℝ F := FiniteDimensional.of_fact_finrank_eq_succ n
  let V := (ℝ ∙ (b : F))ᗮ
  let g : E → V := fun x => stereoToFun (b : F) (f x)
  let t : Set E := {x | x ∈ s ∧ f x ≠ (b : F)}
  have hb : ‖(b : F)‖ = 1 := norm_eq_of_mem_sphere b
  have hdV : finrank ℝ V = n :=
    finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere b)
  have hg (x : E) (hx : x ∈ t) : ContDiffAt ℝ 1 g x := by
    have hx' : innerSL ℝ (b : F) (f x) ≠ 1 := by
      intro heq
      exact hx.2 ((inner_eq_one_iff_of_norm_eq_one hb (hs x hx.1)).mp heq).symm
    have ho : IsOpen {z : F | innerSL ℝ (b : F) z ≠ 1} :=
      (isClosed_eq (innerSL ℝ (b : F)).continuous continuous_const).isOpen_compl
    exact (contDiffOn_stereoToFun (n := 1)).contDiffAt (ho.mem_nhds hx') |>.comp x hf.contDiffAt
  have hdimImage : dimH (g '' t) < finrank ℝ V := by
    calc
      dimH (g '' t) ≤ dimH t := dimH_image_le_of_locally_lipschitzOn (by
        intro x hx
        obtain ⟨K, u, hu, hK⟩ := (hg x hx).exists_lipschitzOnWith
        exact ⟨K, u, mem_nhdsWithin_of_mem_nhds hu, hK⟩)
      _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
      _ = finrank ℝ E := Real.dimH_univ_eq_finrank E
      _ < finrank ℝ V := by rw [hdV]; exact_mod_cast hdim
  obtain ⟨w, hw⟩ := (dense_compl_of_dimH_lt_finrank hdimImage).nonempty
  let e := stereographic hb
  let y : Metric.sphere (0 : F) 1 := e.symm w
  have hy : y ∈ e.source := e.map_target (by simp [e])
  have hby : b ≠ y := by
    have hyb : y ≠ b := by simpa [e] using hy
    exact hyb.symm
  refine ⟨y, hby, ?_⟩
  intro x hx hxy
  apply hw
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · intro hxb
    exact hby (Subtype.ext (hxb.symm.trans hxy))
  · change stereoToFun (b : F) (f x) = w
    rw [hxy]
    exact e.right_inv (by simp [e])

end KIP126.Topology.Sphere
