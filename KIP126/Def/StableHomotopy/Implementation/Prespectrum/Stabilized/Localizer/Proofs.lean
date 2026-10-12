module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Localizer.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Localizer.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The concrete telescope resolution proves the actual full inclusion
is an equivalence after stable localization. -/
instance stabilizedInclusionLocalizer_isLocalizedEquivalence :
    stabilizedInclusionLocalizer.{u}.IsLocalizedEquivalence :=
  stabilizedInclusionLocalizer.isLocalizedEquivalence_of_unit_of_unit
    stabilizedTelescopeLocalizer stabilizedTelescopeRestrictedUnit stabilizedTelescopeUnit
    (fun X => spectrificationTelescopeUnit_stableEquivalence X.obj.obj)
    (fun X => spectrificationTelescopeUnit_stableEquivalence X.obj)

/-- The fixed ordinary source category is the localization of these
actual stabilized T₁ objects. -/
instance stabilizedInclusion_source_isLocalization :
    (stabilizedInclusion.{u} ⋙ t1Inclusion ⋙ sourceLocalization).IsLocalization
      stabilizedStableEquivalences :=
  inferInstanceAs ((stabilizedInclusionLocalizer.functor ⋙
    (t1Inclusion ⋙ sourceLocalization)).IsLocalization _)

end KIP126.StableHomotopy.Implementation.Prespectrum
