module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

private theorem telescope_inclusion_zero (n : ℕ) :
    sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) 0 =
      (2 ^ n : ℕ) • sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n := by
  induction n with
  | zero => simp only [pow_zero,one_smul]
  | succ n ih =>
    have h := sourceHomotopyColimitInclusion_step (sourceScalarSequence 2 (sourceSphere 0)) n
    rw [sourceScalarSequence_step] at h
    change ((2 : ℕ) • 𝟙 (sourceSphere 0)) ≫
      sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) (n + 1) =
        sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n at h
    rw [Preadditive.nsmul_comp,Category.id_comp] at h
    rw [ih,← h,smul_smul,pow_succ]

private theorem two_pow_surjective (d : ℤ) (n : ℕ) :
    Function.Surjective (fun x : StableHomotopy sphereInvertTwo d => (2 ^ n : ℕ) • x) := by
  induction n with
  | zero =>
    intro x
    exact ⟨x,by simp only [pow_zero,one_smul]⟩
  | succ n ih =>
    intro x
    obtain ⟨y,hy⟩ := sphereInvertTwo_two_nsmul_bijective d |>.surjective x
    obtain ⟨z,hz⟩ := ih y
    refine ⟨z,?_⟩
    change (2 ^ n : ℕ) • z = y at hz
    change (2 : ℕ) • y = x at hy
    change (2 ^ (n + 1) : ℕ) • z = x
    rw [pow_succ,mul_nsmul,hz,hy]

/-- Every actual telescope class is in the image of the constructed lift
from the original doubled-bond sphere. Finite-stage representability and
actual scalar invertibility remove the two possible denominator powers. -/
theorem sourceSphereInvertTwoHomotopyLift_surjective (d : ℤ) :
    Function.Surjective (sourceSphereInvertTwoHomotopyLift d) := by
  let F := sourceScalarSequence 2 (sourceSphere 0)
  let T := sourceScalarTelescope 2 (sourceSphere 0)
  intro a
  let x : (sourceStableHomotopyAddFunctor d).obj T :=
    (sourceStableHomotopyEquiv T.as.obj d).symm a
  obtain ⟨n,y,hy⟩ := sourceHomotopyColimit_stableHomotopy_exists_rep F d x
  change (sourceStableHomotopyAddFunctor d).obj (sourceSphere 0) at y
  let b : sourceSphere d ⟶ sourceSphere 0 :=
    sourceStableHomotopyEquiv (sourceSphere 0).as.obj d y
  have ha : b ≫ sourceHomotopyColimitInclusion F n = a := by
    have h := sourceStableHomotopyEquiv_natural (sourceHomotopyColimitInclusion F n) d y
    have hy' : (sourceStableHomotopyFunctor d).map (sourceHomotopyColimitInclusion F n) y = x := by
      rw [← sourceStableHomotopyAddFunctor_forget_map]
      exact hy
    change sourceStableHomotopyEquiv T.as.obj d
      ((sourceStableHomotopyFunctor d).map (sourceHomotopyColimitInclusion F n) y) =
        b ≫ sourceHomotopyColimitInclusion F n at h
    rw [hy'] at h
    exact h.symm.trans ((sourceStableHomotopyEquiv T.as.obj d).apply_symm_apply a)
  let z := (sourceStableHomotopyEquiv sphere d).symm (b ≫ (eqToIso sourceSphere_zero).hom)
  obtain ⟨r,_,hr⟩ := exists_representative_stage_ge z 0
  have hb : sourceStableHomotopyAddEquiv sphere d (Quot.mk (StableRelation sphere d) r) ≫
      (eqToIso sourceSphere_zero).inv = b := by
    rw [hr]
    change sourceStableHomotopyEquiv sphere d
      ((sourceStableHomotopyEquiv sphere d).symm (b ≫ (eqToIso sourceSphere_zero).hom)) ≫ _ = _
    rw [Equiv.apply_symm_apply,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  let w : StableHomotopy sphereInvertTwo d :=
    loopClass sphereInvertTwo d r.stage r.dimension r.degree r.loop
  have hw : sourceSphereInvertTwoHomotopyLift d w =
      b ≫ sourceHomotopyColimitInclusion F r.stage := by
    change sourceStableHomotopyAddEquiv sphere d (Quot.mk (StableRelation sphere d) r) ≫
      (eqToIso sourceSphere_zero).inv ≫ sourceHomotopyColimitInclusion F r.stage = _
    rw [← Category.assoc,hb]
  obtain ⟨v,hv⟩ := two_pow_surjective d n ((2 ^ r.stage : ℕ) • w)
  refine ⟨v,?_⟩
  letI : IsIso ((2 : ℕ) • 𝟙 T) := sourceScalarTelescope_scalar_isIso 2 _
  letI := isIso_nsmul_pow_id 2 T n
  apply (cancel_mono ((2 ^ n : ℕ) • 𝟙 T)).mp
  simp only [Preadditive.comp_nsmul,Category.comp_id]
  calc
    (2 ^ n : ℕ) • sourceSphereInvertTwoHomotopyLift d v =
        sourceSphereInvertTwoHomotopyLift d ((2 ^ n : ℕ) • v) :=
      (sourceSphereInvertTwoHomotopyLift_two_pow_nsmul d n v).symm
    _ = sourceSphereInvertTwoHomotopyLift d ((2 ^ r.stage : ℕ) • w) := congrArg _ hv
    _ = (2 ^ r.stage : ℕ) • (b ≫ sourceHomotopyColimitInclusion F r.stage) := by
      rw [sourceSphereInvertTwoHomotopyLift_two_pow_nsmul,hw]
    _ = b ≫ sourceHomotopyColimitInclusion F 0 := by
      rw [telescope_inclusion_zero r.stage,Preadditive.comp_nsmul]
    _ = (2 ^ n : ℕ) • a := by
      rw [← ha,telescope_inclusion_zero n,Preadditive.comp_nsmul]

/-- The specified comparison is bijective on morphisms from every actual
integer source sphere, retaining its original finite-stage formulas. -/
theorem sourceSphereInvertTwoTelescopeComparison_postcomp_bijective (d : ℤ) :
    Function.Bijective (fun a : sourceSphere d ⟶ sourceScalarTelescope 2 (sourceSphere 0) =>
      a ≫ sourceSphereInvertTwoTelescopeComparison) := by
  constructor
  · intro a b hab
    obtain ⟨x,rfl⟩ := sourceSphereInvertTwoHomotopyLift_surjective d a
    obtain ⟨y,rfl⟩ := sourceSphereInvertTwoHomotopyLift_surjective d b
    change sourceSphereInvertTwoHomotopyLift d x ≫ sourceSphereInvertTwoTelescopeComparison =
      sourceSphereInvertTwoHomotopyLift d y ≫ sourceSphereInvertTwoTelescopeComparison at hab
    rw [sourceSphereInvertTwoHomotopyLift_comparison,sourceSphereInvertTwoHomotopyLift_comparison] at hab
    exact congrArg _ ((sourceStableHomotopyEquiv sphereInvertTwo d).injective hab)
  · intro a
    refine ⟨sourceSphereInvertTwoHomotopyLift d ((sourceStableHomotopyEquiv sphereInvertTwo d).symm a),?_⟩
    exact (sourceSphereInvertTwoHomotopyLift_comparison _ _).trans
      ((sourceStableHomotopyEquiv sphereInvertTwo d).apply_symm_apply a)

/-- The original doubled-bond sphere is actually isomorphic to the scalar
telescope of the original sphere. Isomorphism detection uses all original
stable degrees and the constructed comparison, without a Moore-heart or
sphere-degree assumption. -/
theorem sourceSphereInvertTwoTelescopeComparison_isIso :
    IsIso sourceSphereInvertTwoTelescopeComparison := by
  apply (source_isIso_iff_stableHomotopy_bijective _).mpr
  intro d
  let T := sourceScalarTelescope 2 (sourceSphere 0)
  let eT := sourceStableHomotopyEquiv T.as.obj d
  let eS := sourceStableHomotopyEquiv sphereInvertTwo d
  have he : (fun x : StableHomotopy T.as.obj d =>
      (sourceStableHomotopyFunctor d).map sourceSphereInvertTwoTelescopeComparison x) =
      eS.symm ∘ (fun a => a ≫ sourceSphereInvertTwoTelescopeComparison) ∘ eT := by
    funext x
    apply eS.injective
    change eS ((sourceStableHomotopyFunctor d).map sourceSphereInvertTwoTelescopeComparison x) =
      eS (eS.symm (eT x ≫ sourceSphereInvertTwoTelescopeComparison))
    rw [Equiv.apply_symm_apply]
    exact sourceStableHomotopyEquiv_natural sourceSphereInvertTwoTelescopeComparison d x
  change Function.Bijective (fun x : StableHomotopy T.as.obj d =>
    (sourceStableHomotopyFunctor d).map sourceSphereInvertTwoTelescopeComparison x)
  rw [he]
  exact eS.symm.bijective.comp
    ((sourceSphereInvertTwoTelescopeComparison_postcomp_bijective d).comp eT.bijective)

end KIP126.StableHomotopy.Implementation.Prespectrum
