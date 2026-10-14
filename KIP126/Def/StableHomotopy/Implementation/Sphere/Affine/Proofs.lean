module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Affine.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Signs.Proofs
public import KIP126.Def.Topology.LinearIsotopy.Compactification.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology BasedSpace Matrix
open scoped unitInterval OnePoint
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sphereCubeOnePointHomeomorph_point (n : ℕ) :
    sphereCubeOnePointHomeomorph n (sphereLevel (n + 1)).point = ∞ :=
  (exists_sphereLevel_onePoint_cube_homeomorph n).choose_spec.1

theorem sphereCubeOnePointHomeomorph_cube (n : ℕ)
    (t : ((_root_.Cube.boundary (Fin (n + 1)))ᶜ : Set (Fin (n + 1) → I))) :
    sphereCubeOnePointHomeomorph n (sphereCube (n + 1) t.val) =
      (cubeInteriorHomeomorphReal (Fin (n + 1)) t : OnePoint (Fin (n + 1) → ℝ)) :=
  (exists_sphereLevel_onePoint_cube_homeomorph n).choose_spec.2 t

/-- A homotopy fixed at infinity transports to a homotopy fixed at the
original sphere point through the specified original-cube chart. -/
theorem sphereOnePointSelfMap_homotopic (n : ℕ)
    (f g : C(OnePoint (Fin (n + 1) → ℝ), OnePoint (Fin (n + 1) → ℝ)))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞)
    (H : Nonempty (ContinuousMap.HomotopyRel f g {∞})) :
    Nonempty (ContinuousMap.HomotopyRel (sphereOnePointSelfMap n f hf).map
      (sphereOnePointSelfMap n g hg).map {(sphereLevel (n + 1)).point}) := by
  obtain ⟨H⟩ := H
  let e := sphereCubeOnePointHomeomorph n
  refine ⟨{
    toFun := fun z => e.symm (H (z.1, e z.2))
    continuous_toFun := e.symm.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
    map_zero_left := fun x => congrArg e.symm (H.apply_zero _)
    map_one_left := fun x => congrArg e.symm (H.apply_one _)
    prop' := ?_ }⟩
  intro t x hx
  have hx' : x = (sphereLevel (n + 1)).point := Set.mem_singleton_iff.mp hx
  subst x
  apply congrArg e.symm
  exact H.eq_fst t (by change e (sphereLevel (n + 1)).point = ∞; exact sphereCubeOnePointHomeomorph_point n)

/-- A diagonal coordinate-sign map has exactly the original cube
reflection formula, including the collapsed boundary. -/
theorem sphereMatrixSelfMap_sign_diagonal_cube (n : ℕ)
    (ε : Fin (n + 1) → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hd : (Matrix.diagonal ε).det ≠ 0) (t : Fin (n + 1) → I) :
    (sphereMatrixSelfMap n (Matrix.diagonal ε) hd).map (sphereCube (n + 1) t) =
      sphereCube (n + 1) (fun i => if ε i = -1 then unitInterval.symm (t i) else t i) := by
  classical
  let u : Fin (n + 1) → I := fun i => if ε i = -1 then unitInterval.symm (t i) else t i
  have hub : u ∈ _root_.Cube.boundary (Fin (n + 1)) ↔
      t ∈ _root_.Cube.boundary (Fin (n + 1)) := by
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      by_cases h : ε i = -1
      · simpa [u, h, or_comm] using hi
      · simpa [u, h] using hi
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      by_cases h : ε i = -1
      · simpa [u, h, or_comm] using hi
      · simpa [u, h] using hi
  by_cases ht : t ∈ _root_.Cube.boundary (Fin (n + 1))
  · exact (congrArg (sphereMatrixSelfMap n (Matrix.diagonal ε) hd).map
      ((sphereCube (n + 1)).property t ht)).trans
      ((sphereMatrixSelfMap n (Matrix.diagonal ε) hd).point.trans
        ((sphereCube (n + 1)).property u (hub.mpr ht)).symm)
  have hu : u ∉ _root_.Cube.boundary (Fin (n + 1)) := fun h => ht (hub.mp h)
  apply (sphereCubeOnePointHomeomorph n).injective
  change sphereCubeOnePointHomeomorph n
    ((sphereCubeOnePointHomeomorph n).symm
      (onePointMatrixMap (Matrix.diagonal ε) hd (sphereCubeOnePointHomeomorph n (sphereCube (n + 1) t)))) = _
  rw [Homeomorph.apply_symm_apply, sphereCubeOnePointHomeomorph_cube n ⟨t, ht⟩,
    sphereCubeOnePointHomeomorph_cube n ⟨u, hu⟩]
  change ((Matrix.diagonal ε *ᵥ cubeInteriorHomeomorphReal (Fin (n + 1)) ⟨t, ht⟩) :
    OnePoint (Fin (n + 1) → ℝ)) = ↑(cubeInteriorHomeomorphReal (Fin (n + 1)) ⟨u, hu⟩)
  apply congrArg OnePoint.some
  funext i
  rw [Matrix.mulVec_diagonal]
  rcases hε i with hi | hi
  · simp [hi, cubeInteriorHomeomorphReal, u, show (1 : ℝ) ≠ -1 by norm_num]
  · change ε i * intervalInteriorHomeomorphReal ⟨t i, _⟩ =
      intervalInteriorHomeomorphReal ⟨u i, _⟩
    rw [hi, neg_one_mul]
    simpa only [u, hi, ↓reduceIte] using (intervalInteriorHomeomorphReal_symm
      (⟨t i, ⟨fun h => ht ⟨i, Or.inl h⟩, fun h => ht ⟨i, Or.inr h⟩⟩⟩ :
        {t : I // t ≠ 0 ∧ t ≠ 1})).symm

/-- The actual affine self-map of the original sphere represents the
positive or negative original sphere generator. The proof uses the
constructed affine isotopy and the original cubical reflection formula. -/
theorem sphereSelfMapClass_affine_eq_signed_generator (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.det ≠ 0)
    (b : Fin (n + 1) → ℝ) :
    sphereSelfMapClass (n + 1) (sphereAffineSelfMap n A hA b) = sphereGenerator ∨
      sphereSelfMapClass (n + 1) (sphereAffineSelfMap n A hA b) = -sphereGenerator := by
  obtain ⟨ε, hε, hd, H⟩ := exists_onePointAffineMap_homotopy_sign_diagonal A hA b
  have he := sphereSelfMapClass_homotopic (n + 1) _ _
    (sphereOnePointSelfMap_homotopic n _ _ rfl rfl H)
  change sphereSelfMapClass (n + 1) (sphereAffineSelfMap n A hA b) =
    sphereSelfMapClass (n + 1) (sphereMatrixSelfMap n (Matrix.diagonal ε) hd) at he
  rw [he]
  apply sphereSelfMapClass_eq_signed_generator_of_cube_signs (n + 1)
    (Finset.univ.filter (fun i => ε i = -1))
  intro t
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    sphereMatrixSelfMap_sign_diagonal_cube n ε hε hd t

end KIP126.StableHomotopy.Implementation.Prespectrum
