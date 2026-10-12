module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace KIP126.Topology

open Set Metric
set_option backward.isDefEq.respectTransparency false

/-- Inside any actual Euclidean chart, every open neighborhood contains
a smaller open neighborhood homeomorphic to the full coordinate space.
It is obtained from a genuine metric ball in the given coordinates. -/
theorem exists_euclidean_neighborhood_within
    {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Set Y) (hW : IsOpen W) (e : W ≃ₜ E)
    (y : W) (U : Set Y) (hU : IsOpen U) (hyU : y.val ∈ U) :
    ∃ V : Set Y, y.val ∈ V ∧ IsOpen V ∧ V ⊆ U ∩ W ∧ Nonempty (V ≃ₜ E) := by
  let A : Set E := e '' (Subtype.val ⁻¹' U)
  have hA : IsOpen A := e.isOpenMap _ (hU.preimage continuous_subtype_val)
  have hyA : e y ∈ A := ⟨y, hyU, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hA _ hyA
  let B : Set E := Metric.ball (e y) r
  let V : Set Y := Subtype.val '' (e.symm '' B)
  have hyV : y.val ∈ V :=
    ⟨y, ⟨e y, Metric.mem_ball_self hr, e.symm_apply_apply y⟩, rfl⟩
  have hV : IsOpen V := hW.isOpenMap_subtype_val _
    (e.symm.isOpenMap _ Metric.isOpen_ball)
  have hVU : V ⊆ U ∩ W := by
    rintro z ⟨w, ⟨b, hb, hbw⟩, hwz⟩
    subst z
    refine ⟨?_, w.property⟩
    obtain ⟨w', hw'U, hew'⟩ := hball hb
    have hww' : w = w' := hbw.symm.trans (by rw [← hew', e.symm_apply_apply])
    exact hww' ▸ hw'U
  let b : E ≃ₜ B := Homeomorph.unitBall.trans
    (OpenPartialHomeomorph.unitBallBall (e y) r hr).toHomeomorphSourceTarget
  let a : B ≃ₜ V := (e.symm.image B).trans
    (_root_.Topology.IsEmbedding.subtypeVal.homeomorphImage (e.symm '' B))
  exact ⟨V, hyV, hV, hVU, ⟨a.symm.trans b.symm⟩⟩

end KIP126.Topology
