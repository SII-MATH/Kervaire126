module

public import KIP126.Def.CategoryTheory.Localization.Pi.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Fractions.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Contraction.Proofs
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Localization.Composition

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory HomotopicalAlgebra

universe w u

set_option backward.isDefEq.respectTransparency false

variable (J : Type w)

/-- Families of actual strict homotopies form a quotient localization at
the maps already invertible in the actual homotopy category. -/
theorem pi_homotopyQuotient_isLocalization :
    (Functor.pi (fun (_ : J) => homotopyQuotient.{u})).IsLocalization
      ((MorphismProperty.isomorphisms (J → HomotopyCategory.{u})).inverseImage
        (Functor.pi (fun (_ : J) => homotopyQuotient.{u}))) := by
  let Q := Functor.pi (fun (_ : J) => homotopyQuotient.{u})
  let W := (MorphismProperty.isomorphisms (J → HomotopyCategory.{u})).inverseImage Q
  letI : Q.Full :=
    { map_surjective := fun f => by
        choose g hg using fun j => homotopyQuotient_map_surjective (f j)
        exact ⟨g, funext hg⟩ }
  letI : Q.EssSurj :=
    { mem_essImage := fun Y => ⟨fun j => (Y j).as, ⟨Iso.refl _⟩⟩ }
  apply Functor.isLocalization_of_essSurj_of_full_of_exists_pathObjects Q W
    (fun _ _ _ hf => hf)
  intro X Y f g h
  let H j := ((homotopyQuotient_map_eq_iff (f j) (g j)).mp (congrFun h j)).some
  let P : PrepathObject Y :=
    { P := fun j => pathPrespectrum (Y j)
      p₀ := fun j => pathEvaluation (Y j) 0
      p₁ := fun j => pathEvaluation (Y j) 1
      ι := fun j => pathConstant (Y j)
      ι_p₀ := funext (fun j => pathConstant_comp_evaluation (Y j) 0)
      ι_p₁ := funext (fun j => pathConstant_comp_evaluation (Y j) 1) }
  refine ⟨P, ⟨fun j => (H j).hom, funext (fun j => (H j).zero),
    funext (fun j => (H j).one)⟩, ?_⟩
  change IsIso (Q.map P.ι)
  rw [isIso_pi_iff]
  intro j
  exact homotopyQuotient_pathConstant_isIso (Y j)

/-- The actual localization at stable equivalences commutes with arbitrary
families of prespectra as a localization functor. -/
theorem pi_sourceLocalization_isLocalization :
    (Functor.pi (fun (_ : J) => sourceLocalization.{u})).IsLocalization
      (MorphismProperty.pi (fun (_ : J) => stableEquivalences.{u})) := by
  let Q := Functor.pi (fun (_ : J) => homotopyQuotient.{u})
  let L := Functor.pi (fun (_ : J) => homotopyToSource.{u})
  let W₁ := (MorphismProperty.isomorphisms (J → HomotopyCategory.{u})).inverseImage Q
  let W₂ := MorphismProperty.pi (fun (_ : J) => homotopyStableEquivalences.{u})
  let W := MorphismProperty.pi (fun (_ : J) => stableEquivalences.{u})
  letI : Q.IsLocalization W₁ := pi_homotopyQuotient_isLocalization J
  letI : L.IsLocalization W₂ := KIP126.Foundation.pi_isLocalization_of_hasRightCalculus
    (fun (_ : J) => homotopyToSource) (fun _ => homotopyStableEquivalences)
  have h : (Q ⋙ L).IsLocalization W := by
    apply Functor.IsLocalization.comp Q L W₁ W₂ W
    · exact MorphismProperty.IsInvertedBy.pi _ _
        (fun _ => stableEquivalences.Q_inverts)
    · intro X Y f hf j
      change IsIso (Q.map f) at hf
      haveI : IsIso (homotopyQuotient.map (f j)) := (isIso_pi_iff _).mp hf j
      apply (stableEquivalence_iff_source_isIso (f j)).mpr
      exact inferInstanceAs (IsIso (homotopyToSource.map (homotopyQuotient.map (f j))))
    · intro X Y f hf
      choose g hg using fun j => homotopyQuotient_map_surjective (f j)
      refine ⟨fun j => (X j).as, fun j => (Y j).as, g, ?_, ?_⟩
      · intro j
        apply (homotopyStableEquivalences_map_iff (g j)).mp
        rw [hg j]
        exact hf j
      · have he : Q.map g = f := funext hg
        exact ⟨eqToIso (congrArg Arrow.mk he)⟩
  exact h

end KIP126.StableHomotopy.Implementation.Prespectrum
