module

public import KIP126.Def.Topology.Cube.Compression.Loop.Data

@[expose] public section

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
