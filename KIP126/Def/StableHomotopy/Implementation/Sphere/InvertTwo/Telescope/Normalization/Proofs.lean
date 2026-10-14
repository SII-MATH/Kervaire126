module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- At stage zero the original free sphere counit is the actual equality
comparison with the original sphere prespectrum. -/
theorem sourceSphere_freeCounit_zero :
    freeCounit sphere 0 = eqToHom sourceSpherePrespectrum_zero := by
  apply (freeEvaluation 0 (sphereLevel 0) sphere).injective
  change (freeEvaluation 0 (sphereLevel 0) sphere)
    ((freeEvaluation 0 (sphereLevel 0) sphere).symm (𝟙 _)) = _
  rw [Equiv.apply_symm_apply]
  have h := freeEvaluation_natural 0 (sphereLevel 0) (𝟙 (free 0 (sphereLevel 0)))
    (eqToHom sourceSpherePrespectrum_zero)
  rw [Category.id_comp,freeEvaluation_id] at h
  rw [h]
  change 𝟙 (sphereLevel 0) = eqToHom (free_level 0 (sphereLevel 0)).symm ≫
    (evaluationFunctor 0).map (eqToHom sourceSpherePrespectrum_zero)
  rw [eqToHom_map,eqToHom_trans]
  rfl

private theorem sphere_genLoopFreeSphereMap_cube (n : ℕ) :
    genLoopFreeSphereMap sphere n n (sphereCube n) = freeCounit sphere n := by
  apply ((genLoop_freeSphere_map_exists_unique sphere n n (sphereCube n)).choose_spec.2 _ _).symm
  intro t
  have h := freeEvaluation_natural n (sphereLevel n) (𝟙 (free n (sphereLevel n)))
    (freeCounit sphere n)
  rw [Category.id_comp] at h
  have hf : freeEvaluation n (sphereLevel n) sphere (freeCounit sphere n) =
      𝟙 (sphereLevel n) := Equiv.apply_symm_apply _ _
  rw [hf] at h
  exact (congrArg (fun a : sphereLevel n ⟶ sphereLevel n => a.map (sphereCube n t)) h).symm

/-- The original cubical generator represents the specified actual
comparison from the normalized source S⁰ to the sphere prespectrum. -/
theorem sourceSphere_generator_sourceMap :
    sourceStableHomotopyAddEquiv sphere 0 sphereGenerator =
      (eqToIso sourceSphere_zero).hom := by
  change (sourceFreeSphereDegreeIso 0 0 0 (by omega)).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap sphere 0 0 (sphereCube 0)) = _
  rw [sphere_genLoopFreeSphereMap_cube,sourceSphere_freeCounit_zero,eqToHom_map]
  simp only [sourceFreeSphereDegreeIso,sourceFreeSphereNormalizeIso,Iso.trans_inv,
    eqToIso.inv,eqToIso.hom,eqToHom_trans]

/-- Every original free counit for the sphere is exactly its specified
normalization, followed by the original sphere comparison. -/
theorem sourceSphere_freeCounit_normalization (n : ℕ) :
    sourceLocalization.map (freeCounit sphere n) =
      (sourceFreeSphereDegreeIso 0 n n (by omega)).hom ≫ (eqToIso sourceSphere_zero).hom := by
  apply (cancel_epi (sourceFreeSphereDegreeIso 0 n n (by omega)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  have h : (sourceFreeSphereDegreeIso 0 n n (by omega)).inv ≫
      sourceLocalization.map (freeCounit sphere n) =
      sourceStableHomotopyAddEquiv sphere 0 (loopClass sphere 0 n n (by omega) (sphereCube n)) := by
    change _ = (sourceFreeSphereDegreeIso 0 n n _).inv ≫
      sourceLocalization.map (genLoopFreeSphereMap sphere n n (sphereCube n))
    rw [sphere_genLoopFreeSphereMap_cube]
  rw [h,sphereCube_loopClass,sourceSphere_generator_sourceMap]

end KIP126.StableHomotopy.Implementation.Prespectrum
