module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Stabilized.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Separation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual T₁ prespectra whose based cubical stabilization maps are all
bijective, with their original strict morphisms. -/
abbrev StabilizedPrespectrum := ObjectProperty.FullSubcategory
  (fun X : T1Prespectrum.{u} => HasBijectiveStabilization X.obj)

instance StabilizedPrespectrum.level_t1Space (X : StabilizedPrespectrum.{u}) (n : ℕ) :
    T1Space (X.obj.obj.level n) := inferInstance

def stabilizedInclusion : StabilizedPrespectrum.{u} ⥤ T1Prespectrum.{u} :=
  ObjectProperty.ι _

def stabilizedStableEquivalences : MorphismProperty StabilizedPrespectrum.{u} :=
  t1StableEquivalences.inverseImage stabilizedInclusion

/-- The actual mapping-cylinder telescope, now with its proved target
properties recorded as an object of the full subcategory. -/
noncomputable def stabilizedTelescope : T1Prespectrum.{u} ⥤ StabilizedPrespectrum.{u} where
  obj X := ⟨⟨spectrificationTelescope X.obj, fun _ => inferInstance⟩,
    spectrificationTelescope_hasBijectiveStabilization X.obj⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk (spectrificationTelescopeMap f.hom))
  map_id X := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (spectrificationTelescopeMap_id X.obj))
  map_comp f g := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (spectrificationTelescopeMap_comp f.hom g.hom))

noncomputable def stabilizedTelescopeUnit :
    𝟭 T1Prespectrum.{u} ⟶ stabilizedTelescope ⋙ stabilizedInclusion where
  app X := ObjectProperty.homMk (spectrificationTelescopeUnit X.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (spectrificationTelescopeUnit_natural f.hom)

noncomputable def stabilizedTelescopeRestrictedUnit :
    𝟭 StabilizedPrespectrum.{u} ⟶ stabilizedInclusion ⋙ stabilizedTelescope where
  app X := ObjectProperty.homMk (ObjectProperty.homMk (spectrificationTelescopeUnit X.obj.obj))
  naturality _ _ f := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (spectrificationTelescopeUnit_natural f.hom.hom))

end KIP126.StableHomotopy.Implementation.Prespectrum
