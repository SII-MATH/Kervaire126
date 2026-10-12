module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Proofs
public import KIP126.Def.Topology.Cube.Compression.Loop

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

/-- The actual self-map of the fixed iterated-suspension sphere obtained
by expanding a chosen subcube and collapsing its exterior to the point. -/
noncomputable def sphereWindowCompression (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) : sphereLevel n ⟶ sphereLevel n :=
  (genLoop_sphereLevel_map_exists_unique n (sphereLevel n)
    (KIP126.Topology.Cube.windowCompressedLoop a b hab (sphereCube n))).choose

end KIP126.StableHomotopy.Implementation.Prespectrum
