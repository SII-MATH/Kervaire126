module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Stages.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual doubled bonding map identifies the n-th cube with twice
the next cube. Thus these specified maps are the compatible stages for
the scalar-two telescope of the original source sphere. -/
theorem sourceSphereInvertTwoStage_step (n : ℕ) :
    ((2 : ℕ) • 𝟙 (sourceSphere 0)) ≫ sourceSphereInvertTwoStage (n + 1) =
      sourceSphereInvertTwoStage n := by
  rw [Preadditive.nsmul_comp, Category.id_comp]
  unfold sourceSphereInvertTwoStage
  rw [← map_nsmul]
  apply congrArg (sourceStableHomotopyAddEquiv sphereInvertTwo 0)
  symm
  calc
    loopClass sphereInvertTwo 0 n n (by omega) (sphereCube n) =
        loopClass sphereInvertTwo 0 (n + 1) (n + 1) (by omega)
          (stabilizeLoop sphereInvertTwo n n (sphereCube n)) :=
      Quot.sound (StableRelation.stabilization (⟨n, n, by omega, sphereCube n⟩ :
        Representative sphereInvertTwo 0))
    _ = 2 • loopClass sphereInvertTwo 0 (n + 1) (n + 1) (by omega) (sphereCube (n + 1)) := by
      rw [sphereInvertTwo_stabilizeLoop, loopClass_transAt]
      simp only [sphereCube, two_nsmul]

/-- The specified stage map retains exactly the original free counit;
this formula is needed to compare every degree, not just the zero-stem
generators, with the scalar telescope. -/
theorem sourceSphereInvertTwoStage_freeCounit (n : ℕ) :
    sourceSphereInvertTwoStage n = (sourceFreeSphereDegreeIso 0 n n (by omega)).inv ≫
      sourceLocalization.map (freeCounit sphereInvertTwo n) := by
  have hgen : genLoopFreeSphereMap sphereInvertTwo n n (sphereCube n) =
      freeCounit sphereInvertTwo n := by
    apply ((genLoop_freeSphere_map_exists_unique sphereInvertTwo n n
      (sphereCube n)).choose_spec.2 _ _).symm
    intro t
    have h := freeEvaluation_natural n (sphereLevel n) (𝟙 (free n (sphereLevel n)))
      (freeCounit sphereInvertTwo n)
    rw [Category.id_comp] at h
    have hf : freeEvaluation n (sphereLevel n) sphereInvertTwo (freeCounit sphereInvertTwo n) =
        𝟙 (sphereLevel n) := Equiv.apply_symm_apply _ _
    rw [hf] at h
    exact (congrArg (fun a : sphereLevel n ⟶ sphereLevel n => a.map (sphereCube n t)) h).symm
  change (sourceFreeSphereDegreeIso 0 n n _).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap sphereInvertTwo n n (sphereCube n)) = _
  rw [hgen]

end KIP126.StableHomotopy.Implementation.Prespectrum
