module

public import KIP126.Def.Topology.Cube.Compression.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The actual affine inclusion of the closed unit cube into a chosen
coordinate window. -/
noncomputable def windowExpansion {N : Type*} (a b : N → I) : C((N → I), (N → I)) :=
  ⟨fun u i => Set.Icc.convexComb (a i) (b i) (u i),
    continuous_pi fun i => (Set.Icc.continuous_convexComb (a i) (b i)).comp
      (continuous_apply i)⟩

end KIP126.Topology.Cube
