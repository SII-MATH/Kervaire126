module

public import KIP126.Def.CategoryTheory.Preadditive.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Predicates
public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Shift.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits Prespectrum

/-- An object with invertible doubling is actually HF₂-acyclic: its map
to the zero object induces bijections on every fixed coefficient shift. -/
theorem hf2Equivalence_zero_of_two_id_isIso (A : SourceCategory.{0})
    [IsIso ((2 : ℕ) • 𝟙 A)] :
    HF2Equivalences (0 : A ⟶ sourceLocalization.obj zeroPrespectrum) := by
  intro d
  letI := KIP126.Foundation.hom_subsingleton_of_nsmul_id_isIso
    A (sourceHF2Shift d) 2 (sourceHF2Shift_two_id d)
  constructor
  · intro f g _
    exact source_zeroPrespectrum_isZero.eq_of_src f g
  · intro f
    exact ⟨0, Subsingleton.elim _ _⟩

/-- HF₂ locality kills actual maps from any object with invertible doubling. -/
theorem SourceIsHF2Local.hom_subsingleton_of_two_id_isIso
    {X : SourceCategory.{0}} (hX : SourceIsHF2Local X)
    (A : SourceCategory.{0}) [IsIso ((2 : ℕ) • 𝟙 A)] : Subsingleton (A ⟶ X) := by
  have hs := (hX (0 : A ⟶ sourceLocalization.obj zeroPrespectrum)
    (hf2Equivalence_zero_of_two_id_isIso A)).surjective
  have hz (f : A ⟶ X) : f = 0 := by
    obtain ⟨g,hg⟩ := hs f
    change (0 : A ⟶ sourceLocalization.obj zeroPrespectrum) ≫ g = f at hg
    simpa only [zero_comp] using hg.symm
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

/-- Every HF₂-local prespectrum is 2-complete for the original doubled-bond
sphere and every specified positive and negative suspension iterate. -/
theorem Prespectrum.IsHF2Local.isTwoComplete {X : Prespectrum.{0}}
    (hX : X.IsHF2Local) : X.IsTwoComplete := by
  intro n
  letI := sphereInvertTwo_suspension_two_id_isIso n
  letI := sphereInvertTwo_desuspension_two_id_isIso n
  exact ⟨SourceIsHF2Local.hom_subsingleton_of_two_id_isIso hX _,
    SourceIsHF2Local.hom_subsingleton_of_two_id_isIso hX _⟩

/-- Every value of an actual HF₂ reflection is 2-complete. -/
theorem CompletionModel.replacement_isTwoComplete (L : CompletionModel)
    (X : Prespectrum.{0}) : (L.replacement.obj X).IsTwoComplete :=
  Prespectrum.IsHF2Local.isTwoComplete (L.isLocal X)

end KIP126.StableHomotopy.Implementation
