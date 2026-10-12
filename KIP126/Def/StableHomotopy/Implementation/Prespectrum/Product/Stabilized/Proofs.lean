module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Colimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Localization.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Stabilized.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Stabilization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

variable {J : Type}

/-- Bijective actual stabilization is closed under arbitrary pointwise products. -/
theorem hasBijectiveStabilization_pi (X : J → Prespectrum.{u})
    (hX : ∀ j, HasBijectiveStabilization (X j)) :
    HasBijectiveStabilization (piPrespectrum X) := by
  intro n r
  constructor
  · intro p q h
    apply (levelPiComparison_bijective X n r).injective
    funext j
    apply (hX j n r).injective
    have he := congrArg (fun x => levelPiComparison X (n+1) (r+1) x j) h
    simpa only [levelPiComparison_stabilize] using he
  · intro y
    choose p hp using fun j => (hX j n r).surjective (levelPiComparison X (n+1) (r+1) y j)
    obtain ⟨q,hq⟩ := (levelPiComparison_bijective X n r).surjective p
    refine ⟨q,(levelPiComparison_bijective X (n+1) (r+1)).injective ?_⟩
    rw [levelPiComparison_stabilize,hq]
    exact funext hp

/-- For bijectively stabilized actual prespectra, the original stable homotopy
comparison commutes with arbitrary products, with no finite-index condition. -/
theorem stablePiComparison_bijective_of_stabilization (X : J → Prespectrum.{u})
    (hX : ∀ j, HasBijectiveStabilization (X j)) (d : ℤ) :
    Function.Bijective (stablePiComparison X d) := by
  have hP := (hasBijectiveStabilization_pi X hX).stableLevelClass_zero_bijective d
  have hc (p : stableLevelGroup (piPrespectrum X) d 0) (j : J) :
      stablePiComparison X d (stableLevelClass (piPrespectrum X) d 0 p) j =
        stableLevelClass (X j) d 0
          (levelPiComparison X (stableGroupStage d 0) (stableGroupDimension d 0) p j) :=
    stableLevelClass_natural (piProjection X j) d 0 p
  constructor
  · intro x y h
    obtain ⟨p,rfl⟩ := hP.surjective x
    obtain ⟨q,rfl⟩ := hP.surjective y
    congr 1
    apply (levelPiComparison_bijective X (stableGroupStage d 0) (stableGroupDimension d 0)).injective
    funext j
    apply ((hX j).stableLevelClass_zero_bijective d).injective
    exact (hc p j).symm.trans ((congrFun h j).trans (hc q j))
  · intro y
    choose p hp using fun j => ((hX j).stableLevelClass_zero_bijective d).surjective (y j)
    obtain ⟨q,hq⟩ := (levelPiComparison_bijective X (stableGroupStage d 0)
      (stableGroupDimension d 0)).surjective p
    refine ⟨stableLevelClass (piPrespectrum X) d 0 q,funext fun j => ?_⟩
    exact (hc q j).trans ((congrArg (stableLevelClass (X j) d 0) (congrFun hq j)).trans (hp j))

/-- The constructed telescope satisfies bijective actual stabilization. -/
theorem spectrificationTelescope_hasBijectiveStabilization (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] : HasBijectiveStabilization (spectrificationTelescope X) :=
  spectrificationTelescope_stabilize_bijective X

/-- The actual telescopes remove the uniform-stage obstruction for every
small family, including countable families. -/
theorem stablePiComparison_spectrificationTelescope_bijective (X : J → Prespectrum.{u})
    [∀ j n, T1Space ((X j).level n)] (d : ℤ) :
    Function.Bijective (stablePiComparison (fun j => spectrificationTelescope (X j)) d) :=
  stablePiComparison_bijective_of_stabilization _
    (fun j => spectrificationTelescope_hasBijectiveStabilization (X j)) d

/-- Actual stable equivalences between bijectively stabilized prespectra are
preserved by arbitrary pointwise products. -/
theorem piMap_stableEquivalence_of_stabilization {X Y : J → Prespectrum.{u}}
    (hX : ∀ j, HasBijectiveStabilization (X j)) (hY : ∀ j, HasBijectiveStabilization (Y j))
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences (piMap f) := by
  intro d
  constructor
  · intro x y h
    apply (stablePiComparison_bijective_of_stabilization X hX d).injective
    funext j
    apply (hf j d).injective
    simpa only [stablePiComparison_natural] using
      congrArg (fun z => stablePiComparison Y d z j) h
  · intro y
    choose x hx using fun j => (hf j d).surjective (stablePiComparison Y d y j)
    obtain ⟨z,hz⟩ := (stablePiComparison_bijective_of_stabilization X hX d).surjective x
    refine ⟨z,(stablePiComparison_bijective_of_stabilization Y hY d).injective
      (funext fun j => ?_)⟩
    rw [stablePiComparison_natural,hz]
    exact hx j

end KIP126.StableHomotopy.Implementation.Prespectrum
