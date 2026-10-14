module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Normalization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

private theorem genLoopFreeSphereMap_of_map (X : Prespectrum) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point)
    (f : sphereLevel r ⟶ X.level n) (hf : ∀ t, f.map (sphereCube r t) = p t) :
    genLoopFreeSphereMap X n r p = freeMap n f ≫ freeCounit X n := by
  have he : freeEvaluation n (sphereLevel r) X (freeMap n f ≫ freeCounit X n) = f := by
    rw [freeEvaluation_freeMap_comp]
    change f ≫ (freeEvaluation n (X.level n) X)
      ((freeEvaluation n (X.level n) X).symm (𝟙 _)) = f
    rw [Equiv.apply_symm_apply,Category.comp_id]
  apply ((genLoop_freeSphere_map_exists_unique X n r p).choose_spec.2 _ _).symm
  intro t
  have h := freeEvaluation_natural n (sphereLevel r) (𝟙 (free n (sphereLevel r)))
    (freeMap n f ≫ freeCounit X n)
  rw [Category.id_comp,he] at h
  exact ((congrArg (fun a : sphereLevel r ⟶ X.level n => a.map (sphereCube r t)) h).symm).trans (hf t)

/-- On every actual stable class, composing its constructed lift with the
specified telescope comparison recovers the original representing map. -/
theorem sourceSphereInvertTwoHomotopyLift_comparison (d : ℤ)
    (x : StableHomotopy sphereInvertTwo d) :
    sourceSphereInvertTwoHomotopyLift d x ≫ sourceSphereInvertTwoTelescopeComparison =
      sourceStableHomotopyEquiv sphereInvertTwo d x := by
  induction x using Quot.inductionOn with
  | h a =>
    rcases a with ⟨n, r, hr, p⟩
    obtain ⟨f, hf, _⟩ := genLoop_sphereLevel_map_exists_unique r (sphereLevel n) p
    change (((sourceFreeSphereDegreeIso d n r hr).inv ≫
      sourceLocalization.map (genLoopFreeSphereMap sphere n r p)) ≫
        (eqToIso sourceSphere_zero).inv ≫
          sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n) ≫
            sourceSphereInvertTwoTelescopeComparison =
      (sourceFreeSphereDegreeIso d n r hr).inv ≫
        sourceLocalization.map (genLoopFreeSphereMap sphereInvertTwo n r p)
    rw [genLoopFreeSphereMap_of_map sphere n r p f hf,
      genLoopFreeSphereMap_of_map sphereInvertTwo n r p f hf,
      Functor.map_comp,Functor.map_comp,sourceSphere_freeCounit_normalization]
    simp only [Category.assoc,sourceSphereInvertTwoTelescopeComparison_stage,
      sourceSphereInvertTwoStage_freeCounit,Iso.hom_inv_id_assoc]

private theorem lift_transAt_self (d : ℤ) (n r : ℕ) (hr : (r : ℤ) = d + n)
    (i : Fin r) (p : GenLoop (Fin r) (sphereLevel n) (sphereLevel n).point) :
    sourceSphereInvertTwoHomotopyLift d
        (loopClass sphereInvertTwo d n r hr (GenLoop.transAt i p p)) =
      2 • sourceSphereInvertTwoHomotopyLift d (loopClass sphereInvertTwo d n r hr p) := by
  change sourceStableHomotopyAddEquiv sphere d
      (loopClass sphere d n r hr (GenLoop.transAt i p p)) ≫
        (eqToIso sourceSphere_zero).inv ≫
          sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n = _
  rw [loopClass_transAt,(sourceStableHomotopyAddEquiv sphere d).map_add]
  simp only [Preadditive.add_comp,two_nsmul]
  rfl

/-- The actual quotient lift preserves doubling. This is proved on the
original cubes and their actual concatenation, independently of any
injectivity claim about the comparison map. -/
theorem sourceSphereInvertTwoHomotopyLift_two_nsmul (d : ℤ)
    (x : StableHomotopy sphereInvertTwo d) :
    sourceSphereInvertTwoHomotopyLift d (2 • x) =
      2 • sourceSphereInvertTwoHomotopyLift d x := by
  induction x using Quot.inductionOn with
  | h a =>
    have h : (Quot.mk (StableRelation sphereInvertTwo d) a : StableHomotopy sphereInvertTwo d) =
        loopClass sphereInvertTwo d (a.stage + 1) (a.dimension + 1) (by have := a.degree; omega)
          (stabilizeLoop sphereInvertTwo a.stage a.dimension a.loop) :=
      Quot.sound (StableRelation.stabilization a)
    rw [h]
    have ht := lift_transAt_self d (a.stage + 1) (a.dimension + 1)
      (by have := a.degree; omega) (0 : Fin (a.dimension + 1))
      (stabilizeLoop sphereInvertTwo a.stage a.dimension a.loop)
    rw [loopClass_transAt] at ht
    simpa only [two_nsmul] using ht

/-- The same actual lift preserves each dyadic scalar power. -/
theorem sourceSphereInvertTwoHomotopyLift_two_pow_nsmul (d : ℤ) (k : ℕ)
    (x : StableHomotopy sphereInvertTwo d) :
    sourceSphereInvertTwoHomotopyLift d ((2 ^ k : ℕ) • x) =
      (2 ^ k : ℕ) • sourceSphereInvertTwoHomotopyLift d x := by
  induction k generalizing x with
  | zero => simp only [pow_zero,one_smul]
  | succ k ih =>
    rw [pow_succ,mul_nsmul,sourceSphereInvertTwoHomotopyLift_two_nsmul,ih,mul_nsmul]

end KIP126.StableHomotopy.Implementation.Prespectrum
