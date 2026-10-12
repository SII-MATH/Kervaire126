module

public import KIP126.Def.Topology.Cube.Compression.Proofs

@[expose] public section

section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The original loop, supported in the chosen subcube by actual
coordinate compression. -/
noncomputable def windowCompressedLoop {N X : Type*} [TopologicalSpace X] {x₀ : X}
    (a b : N → I) (hab : ∀ i, a i < b i) (p : GenLoop N X x₀) : GenLoop N X x₀ :=
  ⟨p.val.comp (windowCompression a b), fun x hx =>
    p.property _ (windowCompression_preserves_boundary a b hab x hx)⟩

/-- The original loop and its actual compressed representative are
connected by a continuous homotopy fixed on the full original boundary. -/
noncomputable def windowCompressionLoopHomotopy {N X : Type*} [TopologicalSpace X] {x₀ : X}
    (a b : N → I) (hab : ∀ i, a i < b i) (p : GenLoop N X x₀) :
    ContinuousMap.HomotopyRel p.val (windowCompressedLoop a b hab p).val
      (_root_.Cube.boundary N) where
  toFun z := p (windowCompressionInterpolation a b z)
  continuous_toFun := p.val.continuous.comp (windowCompressionInterpolation a b).continuous
  map_zero_left x := congrArg p (windowCompressionInterpolation_zero a b x)
  map_one_left x := congrArg p (windowCompressionInterpolation_one a b x)
  prop' s x hx := (p.property _
    (windowCompressionInterpolation_preserves_boundary a b hab s x hx)).trans (p.property x hx).symm

end KIP126.Topology.Cube

end

section

namespace KIP126.Topology.Cube

open scoped unitInterval

variable {N X : Type*} [TopologicalSpace X] {x₀ : X}
  (a b : N → I) (hab : ∀ i, a i < b i) (p : GenLoop N X x₀)

theorem windowCompressedLoop_homotopic :
    GenLoop.Homotopic p (windowCompressedLoop a b hab p) :=
  ⟨windowCompressionLoopHomotopy a b hab p⟩

/-- Outside the open chosen subcube the actual compressed loop is
exactly the original basepoint, not merely homotopic to it. -/
theorem windowCompressedLoop_eq_point_outside (x : N → I)
    (hx : ¬ ∀ i, a i < x i ∧ x i < b i) :
    windowCompressedLoop a b hab p x = x₀ := by
  classical
  have hx' : ∃ i, x i ≤ a i ∨ b i ≤ x i := by
    simpa only [not_forall, not_and_or, not_lt] using hx
  obtain ⟨i, hi | hi⟩ := hx'
  · exact p.property _ ⟨i, Or.inl (windowCompression_apply_of_le a b hab x i hi)⟩
  · exact p.property _ ⟨i, Or.inr (windowCompression_apply_of_ge a b hab x i hi)⟩

end KIP126.Topology.Cube

end
