module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Localizer.Data
public import KIP126.Def.CategoryTheory.Localization.Counit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual T₁ replacement proves that the full T₁ inclusion induces
an equivalence of stable localizations. -/
instance t1InclusionLocalizer_isLocalizedEquivalence :
    t1InclusionLocalizer.{u}.IsLocalizedEquivalence :=
  KIP126.Foundation.isLocalizedEquivalence_of_counit_of_counit
    t1InclusionLocalizer cubicalT1Localizer cubicalT1Comparison
    cubicalReplacementComparison
    (fun X => cubicalReplacementComparison_stableEquivalence X.obj)
    cubicalReplacementComparison_stableEquivalence

/-- Thus the given ordinary source category is also the localization
of actual T₁ prespectra, with no extra replacement hypotheses. -/
instance t1Inclusion_source_isLocalization :
    (t1Inclusion.{u} ⋙ sourceLocalization).IsLocalization t1StableEquivalences :=
  inferInstanceAs ((t1InclusionLocalizer.functor ⋙ sourceLocalization).IsLocalization _)

end KIP126.StableHomotopy.Implementation.Prespectrum
