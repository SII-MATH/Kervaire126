module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Locality.BoundedBelow.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Locality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- On an actual bounded-below input, any specified HF2 reflection agrees
with the actual dyadic Moore completion, retaining both original units.
The original Moore-heart coefficient comparison is still an explicit premise. -/
theorem CompletionModel.exists_moore_iso_of_boundedBelow
    [IsIso sourceModTwoMooreHeartToHF2]
    (M : CompletionModel) (X : Prespectrum.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N →
      Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceLocalization.obj X))) :
    ∃ e : sourceLocalization.obj (M.replacement.obj X) ≅
        sourceMooreCompletion 2 (sourceLocalization.obj X),
      sourceLocalization.map (M.unit.app X) ≫ e.hom =
        sourceMooreCompletionUnit 2 (sourceLocalization.obj X) := by
  let A := sourceLocalization.obj (M.replacement.obj X)
  let B := sourceMooreCompletion 2 (sourceLocalization.obj X)
  let u := sourceLocalization.map (M.unit.app X)
  let v := sourceMooreCompletionUnit 2 (sourceLocalization.obj X)
  have hA : SourceIsHF2Local A := M.isLocal X
  have hB : SourceIsHF2Local B :=
    sourceMooreCompletion_isHF2Local_of_boundedBelow _ N hX
  obtain ⟨a, ha⟩ := (hB u (M.unit_hf2Equivalence X)).surjective v
  obtain ⟨b, hb⟩ := (hA v (sourceMooreCompletionUnit_hf2Equivalence _)).surjective u
  change u ≫ a = v at ha
  change v ≫ b = u at hb
  have hab : a ≫ b = 𝟙 A := by
    apply (hA u (M.unit_hf2Equivalence X)).injective
    change u ≫ (a ≫ b) = u ≫ 𝟙 A
    rw [← Category.assoc, ha, hb, Category.comp_id]
  have hba : b ≫ a = 𝟙 B := by
    apply (hB v (sourceMooreCompletionUnit_hf2Equivalence _)).injective
    change v ≫ (b ≫ a) = v ≫ 𝟙 B
    rw [← Category.assoc, hb, ha, Category.comp_id]
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

/-- The actual reflection unit on a bounded-below input has the dyadic
Moore universal property for targets right orthogonal to every object
with invertible doubling. This theorem does not replace that target
condition by the separate doubled-bond-sphere predicate. -/
theorem CompletionModel.unit_moore_universal_of_boundedBelow
    [IsIso sourceModTwoMooreHeartToHF2]
    (M : CompletionModel) (X : Prespectrum.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N →
      Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceLocalization.obj X)))
    (Y : SourceCategory.{0})
    (hY : ∀ U : SourceCategory.{0}, IsIso (2 • 𝟙 U) → Subsingleton (U ⟶ Y)) :
    Function.Bijective (fun a : sourceLocalization.obj (M.replacement.obj X) ⟶ Y =>
      sourceLocalization.map (M.unit.app X) ≫ a) := by
  obtain ⟨e, he⟩ := M.exists_moore_iso_of_boundedBelow X N hX
  have hi : sourceMooreCompletionUnit 2 (sourceLocalization.obj X) ≫ e.inv =
      sourceLocalization.map (M.unit.app X) := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hv := sourceMooreCompletionUnit_precomp_bijective 2 (sourceLocalization.obj X) Y hY
  constructor
  · intro a b hab
    have h : e.inv ≫ a = e.inv ≫ b := by
      apply hv.injective
      change sourceMooreCompletionUnit 2 (sourceLocalization.obj X) ≫ (e.inv ≫ a) =
        sourceMooreCompletionUnit 2 (sourceLocalization.obj X) ≫ (e.inv ≫ b)
      simpa only [← Category.assoc, hi] using hab
    exact (cancel_epi e.inv).mp h
  · intro a
    obtain ⟨b, hb⟩ := hv.surjective a
    refine ⟨e.hom ≫ b, ?_⟩
    change sourceLocalization.map (M.unit.app X) ≫ (e.hom ≫ b) = a
    rw [← Category.assoc, he]
    exact hb

/-- The original stable lower bound is retained by any HF2 reflection,
conditional on the same original Moore-heart comparison. -/
theorem CompletionModel.replacement_boundedBelow_of_boundedBelow
    [IsIso sourceModTwoMooreHeartToHF2]
    (M : CompletionModel) (X : Prespectrum.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N →
      Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceLocalization.obj X)))
    (d : ℤ) (hd : d < N) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (sourceLocalization.obj (M.replacement.obj X))) := by
  obtain ⟨e, _⟩ := M.exists_moore_iso_of_boundedBelow X N hX
  letI := sourceMooreCompletion_boundedBelow 2 (sourceLocalization.obj X) N hX d hd
  exact (ConcreteCategory.bijective_of_isIso
    ((sourceStableHomotopyAddFunctor d).map e.hom)).injective.subsingleton

/-- In particular every such actual reflection of the original sphere
is connective. The existence of a reflection and the coefficient
comparison are not proved by this specialization. -/
theorem CompletionModel.sphere_connective_of_moore_heart_iso
    [IsIso sourceModTwoMooreHeartToHF2] (M : CompletionModel)
    (d : ℤ) (hd : d < 0) :
    Subsingleton (Prespectrum.StableHomotopy (M.replacement.obj Prespectrum.sphere) d) :=
  M.replacement_boundedBelow_of_boundedBelow Prespectrum.sphere 0
    (fun k hk => Prespectrum.sphere_stableHomotopy_subsingleton_of_neg k hk) d hd

end KIP126.StableHomotopy.Implementation
