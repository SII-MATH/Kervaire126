module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Binary.Stability.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

/-- Localization preserves the original strict coproduct of a family of
cofibrant spectra, with its specified original inclusions. -/
theorem sourceLocalization_preserves_coproduct_of_isCubicallyCofibrant
    {J : Type} (X : J → Prespectrum.{0}) (hX : ∀ j, IsCubicallyCofibrant (X j)) :
    PreservesColimit (Discrete.functor X) sourceLocalization := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
  exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm (sourceStrictSigmaCofan_isColimit X hX)

/-- The original localization's comparison with every original binary
coproduct is invertible, without cofibrancy of the two input spectra. -/
theorem source_coprodComparison_isIso (X Y : Prespectrum.{0}) :
    IsIso (coprodComparison sourceLocalization X Y) := by
  let X' := cubicalReplacementFunctor.obj X
  let Y' := cubicalReplacementFunctor.obj Y
  let a := cubicalReplacementComparison.app X
  let b := cubicalReplacementComparison.app Y
  letI : PreservesColimit (pair X' Y') sourceLocalization :=
    sourceLocalization_preserves_coproduct_of_isCubicallyCofibrant (pairFunction X' Y')
      (fun j => WalkingPair.casesOn j (cubicalReplacement_isCubicallyCofibrant X)
        (cubicalReplacement_isCubicallyCofibrant Y))
  letI := stableEquivalences.Q_inverts a (cubicalReplacementComparison_stableEquivalence X)
  letI := stableEquivalences.Q_inverts b (cubicalReplacementComparison_stableEquivalence Y)
  letI := stableEquivalences.Q_inverts (coprod.map a b)
    (coprodMap_stableEquivalence_general a b
      (cubicalReplacementComparison_stableEquivalence X)
      (cubicalReplacementComparison_stableEquivalence Y))
  exact IsIso.of_isIso_fac_left (coprodComparison_natural sourceLocalization a b).symm

/-- The original stable localization preserves actual binary coproducts. -/
noncomputable instance sourceLocalization_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) sourceLocalization.{0} := by
  letI (X Y : Prespectrum.{0}) := source_coprodComparison_isIso X Y
  exact preservesBinaryCoproducts_of_isIso_coprodComparison sourceLocalization

/-- The original stable localization preserves the actual empty coproduct. -/
noncomputable instance sourceLocalization_preservesInitialObject :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) sourceLocalization.{0} where
  preservesColimit {F} := by
    letI : PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) sourceLocalization :=
      sourceLocalization_preserves_coproduct_of_isCubicallyCofibrant
      (fun j : PEmpty.{1} => F.obj ⟨j⟩) (fun j => nomatch j)
    exact preservesColimit_of_iso_diagram sourceLocalization
      (Discrete.natIsoFunctor (F := F)).symm

/-- The original stable localization preserves all actual finite coproducts. -/
noncomputable instance sourceLocalization_preservesFiniteCoproducts :
    PreservesFiniteCoproducts sourceLocalization.{0} where
  preserves n := PreservesFiniteCoproducts.of_preserves_binary_and_initial sourceLocalization (Fin n)

end KIP126.StableHomotopy.Implementation.Prespectrum
