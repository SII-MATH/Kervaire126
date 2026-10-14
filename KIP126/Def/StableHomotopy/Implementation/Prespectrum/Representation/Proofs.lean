module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

theorem stableHomotopySourceMap_natural {X Y : Prespectrum} (f : X ⟶ Y) (d : ℤ)
    (x : StableHomotopy X d) :
    stableHomotopySourceMap Y d (stableHomotopyMap f d x) =
      stableHomotopySourceMap X d x ≫ sourceLocalization.map f := by
  induction x using Quot.inductionOn with
  | h a =>
    change (a.map f).sourceMap = a.sourceMap ≫ sourceLocalization.map f
    dsimp [Representative.sourceMap,Representative.map]
    rw [genLoopFreeSphereMap_natural,Functor.map_comp,Category.assoc]

theorem stableHomotopySourceMap_generator (d : ℤ) :
    stableHomotopySourceMap (sourceSpherePrespectrum d) d (sourceSphereGenerator d) =
      𝟙 (sourceSphere d) := by
  cases d with
  | ofNat n =>
    change (sourceFreeSphereDegreeIso (Int.ofNat n) 0 n _).inv ≫
      sourceLocalization.map (genLoopFreeSphereMap _ _ _ (freeSphereLoop _ _)) = _
    rw [genLoopFreeSphereMap_id]
    simp [CategoryTheory.Functor.map_id,sourceFreeSphereDegreeIso,
      sourceFreeSphereNormalizeIso,sourceSphere,sourceSpherePrespectrum]
  | negSucc n =>
    change (sourceFreeSphereDegreeIso (Int.negSucc n) (n+1) 0 _).inv ≫
      sourceLocalization.map (genLoopFreeSphereMap _ _ _ (freeSphereLoop _ _)) = _
    rw [genLoopFreeSphereMap_id]
    simp [CategoryTheory.Functor.map_id,sourceFreeSphereDegreeIso,
      sourceFreeSphereNormalizeIso,sourceSphere,sourceSpherePrespectrum]

@[simp] theorem sourceStableHomotopyToHom_app (X : Prespectrum) (d : ℤ)
    (x : StableHomotopy X d) :
    (sourceStableHomotopyToHom d).app (sourceLocalization.obj X) (ULift.up x) =
      stableHomotopySourceMap X d x := by
  dsimp only [sourceStableHomotopyToHom,Localization.Construction.natTransExtension]
  rw [Localization.Construction.NatTransExtension.app_eq]
  rfl

/-- Every morphism from the specified source sphere, including arbitrary localization zigzags, comes from an actual stable cubical class. -/
theorem stableHomotopySourceMap_surjective (X : Prespectrum) (d : ℤ) :
    Function.Surjective (stableHomotopySourceMap X d) := by
  intro f
  refine ⟨(sourceStableHomotopyFunctor d).map f (sourceSphereGenerator d),?_⟩
  have h := congrArg (fun k => k (ULift.up (sourceSphereGenerator d)))
    ((sourceStableHomotopyToHom d).naturality f)
  change (sourceStableHomotopyToHom d).app (sourceLocalization.obj X)
      (ULift.up ((sourceStableHomotopyFunctor d).map f (sourceSphereGenerator d))) =
    (sourceStableHomotopyToHom d).app (sourceSphere d) (ULift.up (sourceSphereGenerator d)) ≫ f at h
  rw [sourceStableHomotopyToHom_app] at h
  change _ = (sourceStableHomotopyToHom d).app
    (sourceLocalization.obj (sourceSpherePrespectrum d))
    (ULift.up (sourceSphereGenerator d)) ≫ f at h
  rw [sourceStableHomotopyToHom_app,stableHomotopySourceMap_generator,Category.id_comp] at h
  exact h

theorem stableHomotopySourceMap_generator_image (X : Prespectrum) (d : ℤ)
    (x : StableHomotopy X d) :
    (sourceStableHomotopyFunctor d).map (stableHomotopySourceMap X d x) (sourceSphereGenerator d) = x := by
  induction x using Quot.inductionOn with
  | h a => exact a.sourceMap_generator

/-- The actual cubical stable quotient is represented by the specified integer sphere in the ordinary source localization. -/
theorem stableHomotopySourceMap_bijective (X : Prespectrum) (d : ℤ) :
    Function.Bijective (stableHomotopySourceMap X d) := by
  refine ⟨?_,stableHomotopySourceMap_surjective X d⟩
  intro x y h
  have hh := congrArg (fun f => (sourceStableHomotopyFunctor d).map f (sourceSphereGenerator d)) h
  simpa only [stableHomotopySourceMap_generator_image] using hh

end KIP126.StableHomotopy.Implementation.Prespectrum
