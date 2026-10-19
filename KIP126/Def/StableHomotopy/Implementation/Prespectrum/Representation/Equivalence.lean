module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The explicit equivalence between actual stable cubical classes and ordinary localized sphere morphisms. No completed-spectrum model or Whitehead premise is used. -/
noncomputable def sourceStableHomotopyEquiv (X : Prespectrum) (d : ℤ) :
    StableHomotopy X d ≃ (sourceSphere d ⟶ sourceLocalization.obj X) :=
  Equiv.ofBijective (stableHomotopySourceMap X d) (stableHomotopySourceMap_bijective X d)

/-- The inverse equivalence evaluates a localized morphism on the actual
stable sphere generator. -/
theorem sourceStableHomotopyEquiv_symm_apply (X : Prespectrum) (d : ℤ)
    (f : sourceSphere d ⟶ sourceLocalization.obj X) :
    (sourceStableHomotopyEquiv X d).symm f =
      (sourceStableHomotopyFunctor d).map f (sourceSphereGenerator d) := by
  have h := stableHomotopySourceMap_generator_image X d
    ((sourceStableHomotopyEquiv X d).symm f)
  change (sourceStableHomotopyFunctor d).map
    (sourceStableHomotopyEquiv X d ((sourceStableHomotopyEquiv X d).symm f))
      (sourceSphereGenerator d) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The representation equivalence is natural for arbitrary morphisms in
the ordinary localization, including inverses and zigzags. -/
theorem sourceStableHomotopyEquiv_natural {X Y : Prespectrum}
    (f : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) (d : ℤ)
    (x : StableHomotopy X d) :
    sourceStableHomotopyEquiv Y d ((sourceStableHomotopyFunctor d).map f x) =
      sourceStableHomotopyEquiv X d x ≫ f := by
  have h := congrArg (fun k => k (ULift.up x))
    ((sourceStableHomotopyToHom d).naturality f)
  change (sourceStableHomotopyToHom d).app (sourceLocalization.obj Y)
      (ULift.up ((sourceStableHomotopyFunctor d).map f x)) =
    (sourceStableHomotopyToHom d).app (sourceLocalization.obj X) (ULift.up x) ≫ f at h
  rw [sourceStableHomotopyToHom_app,sourceStableHomotopyToHom_app] at h
  exact h

/-- A displayed free sphere generator corresponds to the inverse of its
specified normalization isomorphism. -/
theorem sourceStableHomotopyEquiv_freeSphereGenerator (d : ℤ) (n r : ℕ)
    (h : (r : ℤ) = d+n) :
    sourceStableHomotopyEquiv (free n (sphereLevel r)) d (freeSphereGenerator d n r h) =
      (sourceFreeSphereDegreeIso d n r h).inv := by
  change (sourceFreeSphereDegreeIso d n r h).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap _ _ _ (freeSphereLoop _ _)) = _
  rw [genLoopFreeSphereMap_id]
  simp only [CategoryTheory.Functor.map_id,Category.comp_id]

/-- The degree-zero representative is the original point-set sphere. -/
theorem sourceSpherePrespectrum_zero : sourceSpherePrespectrum 0 = sphere :=
  suspensionSpectrum_zeroSphere

theorem sourceSphere_zero : sourceSphere 0 = sourceLocalization.obj sphere :=
  congrArg sourceLocalization.obj sourceSpherePrespectrum_zero

/-- Actual stable vanishing gives vanishing of the represented morphism set
in the ordinary source localization. -/
theorem sourceSphere_hom_subsingleton_of_stableHomotopy_subsingleton
    (X : Prespectrum) (d : ℤ) [Subsingleton (StableHomotopy X d)] :
    Subsingleton (sourceSphere d ⟶ sourceLocalization.obj X) :=
  (sourceStableHomotopyEquiv X d).symm.injective.subsingleton

/-- Conversely, the specified source sphere detects vanishing of the actual
cubical stable quotient. -/
theorem stableHomotopy_subsingleton_of_sourceSphere_hom_subsingleton
    (X : Prespectrum) (d : ℤ) [Subsingleton (sourceSphere d ⟶ sourceLocalization.obj X)] :
    Subsingleton (StableHomotopy X d) :=
  (sourceStableHomotopyEquiv X d).injective.subsingleton

end KIP126.StableHomotopy.Implementation.Prespectrum
