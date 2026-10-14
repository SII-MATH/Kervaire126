module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Actual pointwise suspension on the full category of HF₂-local spectra. -/
noncomputable def suspensionFunctor : CompletedSpectrum ⥤ CompletedSpectrum where
  obj X := ⟨X.spectrum.suspension, Prespectrum.IsHF2Local.suspension X.isLocal⟩
  map f := Prespectrum.sourceSuspensionFunctor.map f
  map_id X := Prespectrum.sourceSuspensionFunctor.map_id (sourceLocalization.obj X.spectrum)
  map_comp f g := Prespectrum.sourceSuspensionFunctor.map_comp f g

/-- Actual padded desuspension on the same category of local spectra. -/
noncomputable def desuspensionFunctor : CompletedSpectrum ⥤ CompletedSpectrum where
  obj X := ⟨X.spectrum.desuspension, Prespectrum.IsHF2Local.desuspension X.isLocal⟩
  map f := Prespectrum.sourceDesuspensionFunctor.map f
  map_id X := Prespectrum.sourceDesuspensionFunctor.map_id (sourceLocalization.obj X.spectrum)
  map_comp f g := Prespectrum.sourceDesuspensionFunctor.map_comp f g

/-- The proved ordinary source unit restricts to actual local spectra. -/
noncomputable def suspensionUnitIso :
    𝟭 CompletedSpectrum ≅ suspensionFunctor ⋙ desuspensionFunctor :=
  NatIso.ofComponents (fun X => {
    hom := Prespectrum.sourceSuspensionEquivalence.unitIso.hom.app (toSource.obj X)
    inv := Prespectrum.sourceSuspensionEquivalence.unitIso.inv.app (toSource.obj X)
    hom_inv_id := Prespectrum.sourceSuspensionEquivalence.unitIso.app (toSource.obj X) |>.hom_inv_id
    inv_hom_id := Prespectrum.sourceSuspensionEquivalence.unitIso.app (toSource.obj X) |>.inv_hom_id })
    (fun f => Prespectrum.sourceSuspensionEquivalence.unitIso.hom.naturality f)

/-- The proved ordinary source counit restricts to actual local spectra. -/
noncomputable def suspensionCounitIso :
    desuspensionFunctor ⋙ suspensionFunctor ≅ 𝟭 CompletedSpectrum :=
  NatIso.ofComponents (fun X => {
    hom := Prespectrum.sourceSuspensionEquivalence.counitIso.hom.app (toSource.obj X)
    inv := Prespectrum.sourceSuspensionEquivalence.counitIso.inv.app (toSource.obj X)
    hom_inv_id := Prespectrum.sourceSuspensionEquivalence.counitIso.app (toSource.obj X) |>.hom_inv_id
    inv_hom_id := Prespectrum.sourceSuspensionEquivalence.counitIso.app (toSource.obj X) |>.inv_hom_id })
    (fun f => Prespectrum.sourceSuspensionEquivalence.counitIso.hom.naturality f)

/-- The actual suspension and padded desuspension give an autoequivalence
of HF₂-local spectra without constructing or assuming a reflection. -/
noncomputable def suspensionEquivalence : CompletedSpectrum ≌ CompletedSpectrum :=
  CategoryTheory.Equivalence.mk suspensionFunctor desuspensionFunctor
    suspensionUnitIso suspensionCounitIso

/-- The inclusion identifies the specified local suspension with the actual
ordinary source suspension. -/
noncomputable def toSource_suspensionIso :
    suspensionFunctor ⋙ toSource ≅ toSource ⋙ Prespectrum.sourceSuspensionFunctor :=
  Iso.refl _

/-- The inclusion identifies the specified local desuspension with the actual
ordinary source desuspension. -/
noncomputable def toSource_desuspensionIso :
    desuspensionFunctor ⋙ toSource ≅ toSource ⋙ Prespectrum.sourceDesuspensionFunctor :=
  Iso.refl _

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
