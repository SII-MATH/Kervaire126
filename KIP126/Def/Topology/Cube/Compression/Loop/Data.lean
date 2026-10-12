module

public import KIP126.Def.Topology.Cube.Compression.Proofs

@[expose] public section

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
