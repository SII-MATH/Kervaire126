module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Localizer.Proofs
public import KIP126.Def.CategoryTheory.Localization.Pi.Localizer.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u w

set_option backward.isDefEq.respectTransparency false

/-- The actual cubical replacement also proves the localization equivalence
for arbitrary families, with a single coherent pointwise functor. -/
instance t1PiInclusionLocalizer_isLocalizedEquivalence (J : Type w) :
    (piLocalizerMorphism (fun _ : J => t1InclusionLocalizer.{u})).IsLocalizedEquivalence :=
  isLocalizedEquivalence_of_counit_of_counit
    (piLocalizerMorphism (fun _ : J => t1InclusionLocalizer))
    (piLocalizerMorphism (fun _ : J => cubicalT1Localizer))
    (NatTrans.pi (fun _ : J => cubicalT1Comparison))
    (NatTrans.pi (fun _ : J => cubicalReplacementComparison))
    (fun X j => cubicalReplacementComparison_stableEquivalence (X j).obj)
    (fun X j => cubicalReplacementComparison_stableEquivalence (X j))

end KIP126.StableHomotopy.Implementation.Prespectrum
