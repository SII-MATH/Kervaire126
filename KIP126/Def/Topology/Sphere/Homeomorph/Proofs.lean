module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace KIP126.Topology.Sphere

open Metric NormedSpace

/-- Radial normalization of an actual continuous linear equivalence
identifies the corresponding unit spheres, including different norms. -/
theorem exists_unitSphere_homeomorph_of_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ∃ h : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1,
      ∀ x, (h x).val = normalize (e x.val) := by
  have hnE (x : Metric.sphere (0 : E) 1) : ‖x.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hnF (y : Metric.sphere (0 : F) 1) : ‖y.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  have hx0 (x : Metric.sphere (0 : E) 1) : e x.val ≠ 0 := by
    intro hx
    have hz := e.injective (hx.trans e.map_zero.symm)
    simpa [hz] using hnE x
  have hy0 (y : Metric.sphere (0 : F) 1) : e.symm y.val ≠ 0 := by
    intro hy
    have hz := e.symm.injective (hy.trans e.symm.map_zero.symm)
    simpa [hz] using hnF y
  refine ⟨{
    toFun := fun x => ⟨normalize (e x.val), by
      simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize (hx0 x)⟩
    invFun := fun y => ⟨normalize (e.symm y.val), by
      simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize (hy0 y)⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun _ => rfl⟩
  · intro x
    apply Subtype.ext
    change normalize (e.symm (‖e x.val‖⁻¹ • e x.val)) = x.val
    rw [map_smul, e.symm_apply_apply,
      normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hx0 x)))]
    exact normalize_eq_self_of_norm_eq_one (hnE x)
  · intro y
    apply Subtype.ext
    change normalize (e (‖e.symm y.val‖⁻¹ • e.symm y.val)) = y.val
    rw [map_smul, e.apply_symm_apply,
      normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hy0 y)))]
    exact normalize_eq_self_of_norm_eq_one (hnF y)
  · apply Continuous.subtype_mk
    exact (((e.continuous.comp continuous_subtype_val).norm.inv₀
      (fun x => norm_ne_zero_iff.mpr (hx0 x))).smul
        (e.continuous.comp continuous_subtype_val))
  · apply Continuous.subtype_mk
    exact (((e.symm.continuous.comp continuous_subtype_val).norm.inv₀
      (fun y => norm_ne_zero_iff.mpr (hy0 y))).smul
        (e.symm.continuous.comp continuous_subtype_val))

/-- An explicit orthogonal reflection takes any chosen point of a real
unit sphere to any other chosen point. -/
theorem exists_unitSphere_homeomorph_apply_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : Metric.sphere (0 : E) 1) :
    ∃ h : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1, h x = y := by
  let r := Submodule.reflection (ℝ ∙ (x.val - y.val))ᗮ
  have hn : ‖x.val‖ = ‖y.val‖ := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property.trans y.property.symm
  have hm (z : E) : z ∈ Metric.sphere (0 : E) 1 ↔ r z ∈ Metric.sphere (0 : E) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, r.norm_map]
  refine ⟨r.toHomeomorph.subtype hm, ?_⟩
  apply Subtype.ext
  exact Submodule.reflection_sub hn

end KIP126.Topology.Sphere
