module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Localizer.Pi.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u w

set_option backward.isDefEq.respectTransparency false

/-- The ordinary family source category is the localization of families
of actual stabilized T₁ prespectra. Both resolutions have been constructed. -/
instance stabilizedPiInclusion_source_isLocalization (J : Type w) :
    (Functor.pi (fun _ : J => stabilizedInclusion.{u} ⋙ t1Inclusion ⋙ sourceLocalization)).IsLocalization
      (MorphismProperty.pi (fun _ : J => stabilizedStableEquivalences)) := by
  letI := pi_sourceLocalization_isLocalization.{w,u} J
  letI : ((piLocalizerMorphism (fun _ : J => t1InclusionLocalizer.{u})).functor ⋙
      Functor.pi (fun _ : J => sourceLocalization)).IsLocalization
        (MorphismProperty.pi (fun _ : J => t1StableEquivalences)) := inferInstance
  exact inferInstanceAs (((piLocalizerMorphism (fun _ : J => stabilizedInclusionLocalizer)).functor ⋙
    ((piLocalizerMorphism (fun _ : J => t1InclusionLocalizer)).functor ⋙
      Functor.pi (fun _ : J => sourceLocalization))).IsLocalization _)

end KIP126.StableHomotopy.Implementation.Prespectrum
