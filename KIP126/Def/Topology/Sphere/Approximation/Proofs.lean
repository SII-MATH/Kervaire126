module

public import KIP126.Def.Topology.Sphere.Nullhomotopy.Proofs
public import KIP126.Def.Topology.Cube.Collar.Proofs
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Relative smooth approximation of cubical loops in a Euclidean sphere.
An explicit collar makes the boundary locally constant before approximation.
Normalization preserves the boundary and gives a homotopy through sphere-valued
maps. Together with the dimension bound, this proves sphere connectivity. -/

namespace KIP126.Topology.Sphere

open Metric Module Set NormedSpace
open scoped unitInterval Topology.Homotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalization is continuous along any map avoiding the origin. -/
theorem continuous_normalize_of_ne_zero {X : Type*} [TopologicalSpace X]
    {f : X → E} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) :
    Continuous (fun x => normalize (f x)) :=
  (hf.norm.inv₀ fun x => norm_ne_zero_iff.mpr (h0 x)).smul hf

/-- A short segment starting at a unit vector never passes through the origin. -/
theorem sphere_segment_ne_zero (x y : E) (hx : ‖x‖ = 1)
    (hxy : dist y x < 1) (s : I) :
    ((1 : ℝ) - (s : ℝ)) • x + (s : ℝ) • y ≠ 0 := by
  have hd : dist (((1 : ℝ) - (s : ℝ)) • x + (s : ℝ) • y) x < 1 := by
    rw [dist_eq_norm]
    have heq : ((1 : ℝ) - (s : ℝ)) • x + (s : ℝ) • y - x =
        (s : ℝ) • (y - x) := by module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) s.property.2) (by simpa only [dist_eq_norm] using hxy)
  intro hzero
  simp [hzero, hx] at hd

/-- Sufficiently close sphere-valued cubical loops are based-homotopic by
normalizing their straight-line interpolation. -/
theorem genLoop_homotopic_of_dist_lt_one {r : ℕ} {b : Metric.sphere (0 : E) 1}
    (p q : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b)
    (hpq : ∀ x, dist (q x : E) (p x : E) < 1) :
    GenLoop.Homotopic p q := by
  let v (z : I × (Fin r → I)) : E :=
    ((1 : ℝ) - (z.1 : ℝ)) • (p z.2 : E) + (z.1 : ℝ) • (q z.2 : E)
  have hv : Continuous v :=
    ((continuous_const.sub continuous_fst.subtype_val).smul
      (p.val.continuous.subtype_val.comp continuous_snd)).add
      (continuous_fst.subtype_val.smul
        (q.val.continuous.subtype_val.comp continuous_snd))
  have h0 (z) : v z ≠ 0 := sphere_segment_ne_zero _ _
    (norm_eq_of_mem_sphere (p z.2)) (hpq z.2) z.1
  have hn (z) : normalize (v z) ∈ Metric.sphere (0 : E) 1 := by
    simpa only [mem_sphere_zero_iff_norm] using norm_normalize (h0 z)
  refine ⟨{
    toFun := fun z => ⟨normalize (v z), hn z⟩
    continuous_toFun := (continuous_normalize_of_ne_zero hv h0).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    apply Subtype.ext
    change normalize (((1 : ℝ) - 0) • (p x : E) + (0 : ℝ) • (q x : E)) = (p x : E)
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using
      normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere (p x))
  · intro x
    apply Subtype.ext
    change normalize (((1 : ℝ) - 1) • (p x : E) + (1 : ℝ) • (q x : E)) = (q x : E)
    simpa only [sub_self, zero_smul, one_smul, zero_add] using
      normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere (q x))
  · intro s x hx
    apply Subtype.ext
    change normalize (((1 : ℝ) - (s : ℝ)) • (p x : E) +
      (s : ℝ) • (q x : E)) = (p x : E)
    have hpx : p x = b := p.property x hx
    have hqx : q x = b := q.property x hx
    rw [hpx, hqx, ← add_smul, sub_add_cancel, one_smul]
    exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere b)

/-- Normalizing a nonzero approximation to a unit vector at most doubles
the error. -/
theorem dist_normalize_le_two_mul (x y : E) (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    dist (normalize y) x ≤ 2 * dist y x := by
  have he : dist (normalize y) y = |‖y‖ - 1| := by
    rw [dist_eq_norm]
    have heq : normalize y - y = (1 - ‖y‖) • normalize y := by
      rw [sub_smul, one_smul, norm_smul_normalize]
    rw [heq, norm_smul]
    rw [norm_normalize hy, mul_one, Real.norm_eq_abs, abs_sub_comm]
  have hb : dist (normalize y) y ≤ dist y x := by
    rw [he, dist_eq_norm, ← hx]
    exact abs_norm_sub_norm_le y x
  calc
    dist (normalize y) x ≤ dist (normalize y) y + dist y x := dist_triangle _ _ _
    _ ≤ 2 * dist y x := by linarith

/-- Every sphere-valued cubical loop is based-homotopic to one admitting a
smooth ambient extension. -/
theorem exists_homotopic_genLoop_smooth_extension {r : ℕ}
    {b : Metric.sphere (0 : E) 1}
    (p : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b) :
    ∃ q : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b,
      GenLoop.Homotopic p q ∧ ∃ f : (Fin r → ℝ) → E,
      ContDiff ℝ 1 f ∧ ∀ t : Fin r → I, f (fun i => (t i : ℝ)) = (q t : E) := by
  obtain ⟨q, hq, hpq⟩ := Cube.exists_collared_loop_homotopic r p
  let F (x : Fin r → ℝ) : E := p (Cube.collar r x)
  have hF : Continuous F := p.val.continuous.subtype_val.comp (Cube.continuous_collar r)
  have hFn (x) : ‖F x‖ = 1 := norm_eq_of_mem_sphere (p (Cube.collar r x))
  let S : Set (Fin r → ℝ) := {x | ∃ i, x i ≤ 0 ∨ 1 ≤ x i}
  let U : Set (Fin r → ℝ) := {x | ∃ i, x i < 1 / 4 ∨ 3 / 4 < x i}
  have hS : IsClosed S := by
    simpa only [S, Set.setOf_exists, Set.setOf_or] using isClosed_iUnion_of_finite fun i : Fin r =>
      (isClosed_le (continuous_apply i) continuous_const).union
        (isClosed_le continuous_const (continuous_apply i))
  have hU : IsOpen U := by
    simpa only [U, Set.setOf_exists, Set.setOf_or] using isOpen_iUnion fun i : Fin r =>
      (isOpen_lt (continuous_apply i) continuous_const).union
        (isOpen_lt continuous_const (continuous_apply i))
  have hSU : S ⊆ U := by
    rintro x ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rcases hi with hi | hi
    · left; linarith
    · right; linarith
  have hFU : EqOn F (fun _ => (b : E)) U := by
    rintro x ⟨i, hi⟩
    change (p (Cube.collar r x) : E) = (b : E)
    apply congrArg Subtype.val (p.property _ ?_)
    refine ⟨i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl (Cube.collarCoordinate_eq_zero hi.le)
    · exact Or.inr (Cube.collarCoordinate_eq_one hi.le)
  have hFd : ContDiffOn ℝ 1 F U := contDiffOn_const.congr hFU
  obtain ⟨g, hg, hgF, hgS, -⟩ := hF.exists_contDiff_approx_and_eqOn 1
    (ε := fun _ => (1 : ℝ) / 4) continuous_const (by intro; norm_num)
    hS (hU.mem_nhdsSet.mpr hSU) hFd
  have hg0 (x) : g x ≠ 0 := by
    intro hx
    have := hgF x
    norm_num [hx, hFn] at this
  let f (x : Fin r → ℝ) := normalize (g x)
  have hfd : ContDiff ℝ 1 f :=
    ((hg.norm ℝ hg0).inv fun x => norm_ne_zero_iff.mpr (hg0 x)).smul hg
  have hfs (x) : f x ∈ Metric.sphere (0 : E) 1 := by
    simpa only [mem_sphere_zero_iff_norm] using norm_normalize (hg0 x)
  have hfb (x) (hx : x ∈ S) : f x = (b : E) := by
    change normalize (g x) = (b : E)
    rw [hgS hx, hFU (hSU hx)]
    exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere b)
  let q' : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b :=
    ⟨⟨fun t => ⟨f (fun i => (t i : ℝ)), hfs _⟩,
      (hfd.continuous.comp (continuous_pi fun i => (continuous_apply i).subtype_val)).subtype_mk _⟩,
      by
        intro t ht
        apply Subtype.ext
        apply hfb
        obtain ⟨i, hi⟩ := ht
        refine ⟨i, ?_⟩
        rcases hi with hi | hi
        · left; simp [hi]
        · right; simp [hi]⟩
  refine ⟨q', hpq.trans (genLoop_homotopic_of_dist_lt_one q q' ?_), f, hfd, fun _ => rfl⟩
  intro t
  change dist (normalize (g (fun i => (t i : ℝ)))) (q t : E) < 1
  rw [hq]
  change dist (normalize (g (fun i => (t i : ℝ)))) (F (fun i => (t i : ℝ))) < 1
  exact lt_of_le_of_lt (dist_normalize_le_two_mul _ _ (hFn _) (hg0 _))
    (by have := hgF (fun i => (t i : ℝ)); linarith)

/-- The Euclidean n-sphere has trivial based homotopy in degrees r < n. -/
theorem genLoop_nullhomotopic_of_lt_dimension {n r : ℕ}
    [Fact (finrank ℝ E = n + 1)] (hrn : r < n)
    {b : Metric.sphere (0 : E) 1}
    (p : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨q, hpq, f, hf, hfp⟩ := exists_homotopic_genLoop_smooth_extension p
  exact hpq.trans (genLoop_nullhomotopic_of_smooth_extension hrn q f hf hfp)

end KIP126.Topology.Sphere
