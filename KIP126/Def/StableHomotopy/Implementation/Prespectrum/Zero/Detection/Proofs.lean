module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Zero.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- An actual source zero object has trivial original stable homotopy groups. -/
theorem stableHomotopy_subsingleton_of_source_isZero (X : Prespectrum.{u})
    (hX : IsZero (sourceLocalization.obj X)) (d : ℤ) :
    Subsingleton (StableHomotopy X d) := by
  have hz (x : StableHomotopy X d) : x = 0 := by
    have h := congrArg (fun f => (sourceStableHomotopyAddFunctor d).map f)
      (hX.eq_zero_of_src (𝟙 (sourceLocalization.obj X)))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h
    exact congrArg (fun f => f x) h
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Vanishing of all original stable groups detects the actual source zero
object, by inverting the strict map to the point prespectrum. -/
theorem source_isZero_of_stableHomotopy_subsingleton (X : Prespectrum.{u})
    (hX : ∀ d : ℤ, Subsingleton (StableHomotopy X d)) :
    IsZero (sourceLocalization.obj X) := by
  have hf : stableEquivalences (0 : X ⟶ zeroPrespectrum) := by
    intro d
    letI := hX d
    letI := stableHomotopy_subsingleton_of_source_isZero zeroPrespectrum
      source_zeroPrespectrum_isZero d
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  letI := (stableEquivalence_iff_source_isIso (0 : X ⟶ zeroPrespectrum)).mp hf
  exact source_zeroPrespectrum_isZero.of_iso
    (asIso (sourceLocalization.map (0 : X ⟶ zeroPrespectrum)))

/-- Stable groups detect zero objects in the original ordinary stable category. -/
theorem source_isZero_iff_stableHomotopy_subsingleton (X : Prespectrum.{u}) :
    IsZero (sourceLocalization.obj X) ↔
      ∀ d : ℤ, Subsingleton (StableHomotopy X d) :=
  ⟨stableHomotopy_subsingleton_of_source_isZero X,
    source_isZero_of_stableHomotopy_subsingleton X⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
