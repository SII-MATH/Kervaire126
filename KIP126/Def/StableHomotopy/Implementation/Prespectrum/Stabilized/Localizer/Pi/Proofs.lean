module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Localizer
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Localizer.Pi.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u w

set_option backward.isDefEq.respectTransparency false

/-- The actual telescope resolves arbitrary families of T₁ prespectra,
so the full stabilized inclusion is a pointwise localized equivalence. -/
instance stabilizedPiInclusionLocalizer_isLocalizedEquivalence (J : Type w) :
    (piLocalizerMorphism (fun _ : J => stabilizedInclusionLocalizer.{u})).IsLocalizedEquivalence :=
  (piLocalizerMorphism (fun _ : J => stabilizedInclusionLocalizer)).isLocalizedEquivalence_of_unit_of_unit
    (piLocalizerMorphism (fun _ : J => stabilizedTelescopeLocalizer))
    (NatTrans.pi (fun _ : J => stabilizedTelescopeRestrictedUnit))
    (NatTrans.pi (fun _ : J => stabilizedTelescopeUnit))
    (fun X j => spectrificationTelescopeUnit_stableEquivalence (X j).obj.obj)
    (fun X j => spectrificationTelescopeUnit_stableEquivalence (X j).obj)

end KIP126.StableHomotopy.Implementation.Prespectrum
