module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Cube.Proofs
public import KIP126.Def.Topology.LinearIsotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology
open scoped OnePoint

/-- The actual one-point chart retaining the original canonical cube
and its coordinate reflections. -/
noncomputable def sphereCubeOnePointHomeomorph (n : ℕ) :
    sphereLevel (n + 1) ≃ₜ OnePoint (Fin (n + 1) → ℝ) :=
  (exists_sphereLevel_onePoint_cube_homeomorph n).choose

/-- Transport a specified infinity-preserving map through the actual
original-cube chart, retaining the original sphere and original point. -/
noncomputable def sphereOnePointSelfMap (n : ℕ)
    (f : C(OnePoint (Fin (n + 1) → ℝ), OnePoint (Fin (n + 1) → ℝ)))
    (hf : f ∞ = ∞) : sphereLevel (n + 1) ⟶ sphereLevel (n + 1) where
  map := ⟨fun x => (sphereCubeOnePointHomeomorph n).symm
    (f (sphereCubeOnePointHomeomorph n x)),
    (sphereCubeOnePointHomeomorph n).symm.continuous.comp
      (f.continuous.comp (sphereCubeOnePointHomeomorph n).continuous)⟩
  point := by
    have he := (exists_sphereLevel_onePoint_cube_homeomorph n).choose_spec.1
    change (sphereCubeOnePointHomeomorph n).symm
      (f (sphereCubeOnePointHomeomorph n (sphereLevel (n + 1)).point)) = _
    rw [show sphereCubeOnePointHomeomorph n (sphereLevel (n + 1)).point = ∞ from he, hf]
    exact (congrArg (sphereCubeOnePointHomeomorph n).symm he).symm.trans
      ((sphereCubeOnePointHomeomorph n).symm_apply_apply _)

/-- An invertible real matrix as an actual self-map of the original
sphere, through its specified cube coordinates. -/
noncomputable def sphereMatrixSelfMap (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.det ≠ 0) : sphereLevel (n + 1) ⟶ sphereLevel (n + 1) :=
  sphereOnePointSelfMap n (onePointMatrixMap A hA) rfl

/-- An invertible affine map as an actual self-map of the original
sphere, through the same specified cube coordinates. -/
noncomputable def sphereAffineSelfMap (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.det ≠ 0) (b : Fin (n + 1) → ℝ) : sphereLevel (n + 1) ⟶ sphereLevel (n + 1) :=
  sphereOnePointSelfMap n (onePointAffineMap A hA b) rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
