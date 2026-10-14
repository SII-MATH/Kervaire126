module

public import KIP126.Def.Topology.Sphere.Image.Proofs
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

/-! Based nullhomotopies in a punctured Euclidean sphere. Stereographic
projection turns the homotopy into the straight-line contraction to the
specified basepoint and therefore fixes the entire cubical boundary. -/

namespace KIP126.Topology.Sphere

open Metric Module
open scoped unitInterval Topology.Homotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A based cubical map avoiding one point of the unit sphere is based
nullhomotopic, provided that the omitted point is not the basepoint. -/
theorem genLoop_nullhomotopic_of_avoids_point {r : ℕ}
    {b : Metric.sphere (0 : E) 1}
    (p : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b)
    (y : Metric.sphere (0 : E) 1) (hby : b ≠ y) (hpy : ∀ t, p t ≠ y) :
    GenLoop.Homotopic p GenLoop.const := by
  let e := stereographic (norm_eq_of_mem_sphere y)
  have hb : b ∈ e.source := by simpa [e] using hby
  have hp (t) : p t ∈ e.source := by simpa [e] using hpy t
  have he : Continuous (fun t => e (p t)) :=
    e.continuousOn.comp_continuous p.val.continuous hp
  have hei : Continuous e.symm := continuousOn_univ.mp (by
    simpa [e] using e.continuousOn_symm)
  refine ⟨{
    toFun := fun z => e.symm (((1 : ℝ) - (z.1 : ℝ)) • e (p z.2) +
      (z.1 : ℝ) • e b)
    continuous_toFun := hei.comp
      (((continuous_const.sub continuous_fst.subtype_val).smul
        (he.comp continuous_snd)).add (continuous_fst.subtype_val.smul continuous_const))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change e.symm (((1 : ℝ) - 0) • e (p t) + (0 : ℝ) • e b) = p t
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using e.left_inv (hp t)
  · intro t
    change e.symm (((1 : ℝ) - 1) • e (p t) + (1 : ℝ) • e b) = b
    simpa only [sub_self, zero_smul, one_smul, zero_add] using e.left_inv hb
  · intro t x hx
    change e.symm (((1 : ℝ) - (t : ℝ)) • e (p x) + (t : ℝ) • e b) = p x
    have hpx : p x = b := p.property x hx
    rw [hpx, ← add_smul, sub_add_cancel, one_smul]
    exact e.left_inv hb

/-- Cubical loops with a smooth ambient extension are nullhomotopic below
the sphere dimension. The extension is only required to be sphere-valued
on the cube itself. -/
theorem genLoop_nullhomotopic_of_smooth_extension {n r : ℕ}
    [Fact (finrank ℝ E = n + 1)] (hrn : r < n)
    {b : Metric.sphere (0 : E) 1}
    (p : GenLoop (Fin r) (Metric.sphere (0 : E) 1) b)
    (f : (Fin r → ℝ) → E) (hf : ContDiff ℝ 1 f)
    (hfp : ∀ t : Fin r → I, f (fun i => (t i : ℝ)) = (p t : E)) :
    GenLoop.Homotopic p GenLoop.const := by
  let cube : Set (Fin r → ℝ) := Set.range (fun t : Fin r → I => fun i => (t i : ℝ))
  have hs : ∀ x ∈ cube, ‖f x‖ = 1 := by
    rintro x ⟨t, rfl⟩
    rw [hfp]
    exact norm_eq_of_mem_sphere (p t)
  obtain ⟨y, hby, hy⟩ := exists_sphere_point_outside_image f hf cube hs
    (by simpa using hrn) b
  apply genLoop_nullhomotopic_of_avoids_point p y hby
  intro t hty
  apply hy (fun i => (t i : ℝ)) ⟨t, rfl⟩
  rw [hfp, hty]

end KIP126.Topology.Sphere
