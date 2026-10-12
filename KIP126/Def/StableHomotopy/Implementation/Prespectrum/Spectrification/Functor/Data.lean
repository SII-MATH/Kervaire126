module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual mapping-cylinder telescope as a functor of strict prespectra. -/
noncomputable def spectrificationTelescopeFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := spectrificationTelescope
  map := spectrificationTelescopeMap
  map_id := spectrificationTelescopeMap_id
  map_comp := spectrificationTelescopeMap_comp

/-- The actual inclusions form the telescope functor's natural unit. -/
noncomputable def spectrificationTelescopeUnitNat : 𝟭 Prespectrum.{u} ⟶ spectrificationTelescopeFunctor where
  app := spectrificationTelescopeUnit
  naturality _ _ := spectrificationTelescopeUnit_natural

end KIP126.StableHomotopy.Implementation.Prespectrum
