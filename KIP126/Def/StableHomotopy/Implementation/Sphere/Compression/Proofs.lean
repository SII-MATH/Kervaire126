module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology.Cube
open scoped unitInterval

@[simp] theorem sphereWindowCompression_cube (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) (t : Fin n → I) :
    (sphereWindowCompression n a b hab).map (sphereCube n t) =
      sphereCube n (windowCompression a b t) :=
  (genLoop_sphereLevel_map_exists_unique n (sphereLevel n)
    (windowCompressedLoop a b hab (sphereCube n))).choose_spec.1 t

/-- The compression is homotopic to the identity of the original fixed
sphere, keeping its original basepoint fixed throughout. -/
theorem sphereWindowCompression_homotopic_id (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    Nonempty (ContinuousMap.HomotopyRel (sphereWindowCompression n a b hab).map
      (ContinuousMap.id (sphereLevel n)) {(sphereLevel n).point}) := by
  have h := (genLoop_homotopic_iff_sphereLevel_maps_homotopic n (sphereLevel n)
    (sphereCube n) (windowCompressedLoop a b hab (sphereCube n))
    (𝟙 (sphereLevel n)) (sphereWindowCompression n a b hab)
    (fun _ => rfl) (sphereWindowCompression_cube n a b hab)).mp
      (windowCompressedLoop_homotopic a b hab (sphereCube n))
  exact ⟨h.some.symm⟩

/-- The same original sphere self-map sends the entire exterior of the
selected open subcube to its basepoint, with an exact pointwise formula. -/
theorem sphereWindowCompression_eq_point_outside (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) (t : Fin n → I)
    (ht : ¬ ∀ i, a i < t i ∧ t i < b i) :
    (sphereWindowCompression n a b hab).map (sphereCube n t) = (sphereLevel n).point := by
  rw [sphereWindowCompression_cube]
  exact windowCompressedLoop_eq_point_outside a b hab (sphereCube n) t ht

end KIP126.StableHomotopy.Implementation.Prespectrum
