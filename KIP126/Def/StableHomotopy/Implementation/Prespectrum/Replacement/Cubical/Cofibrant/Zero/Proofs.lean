module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Iso.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- Maps from any actual zero spectrum to a cofibrant spectrum have
the same proved initial-arrow lifting property. -/
theorem IsCubicallyCofibrant.map_from_isZero {X Y : Prespectrum.{u}}
    (hY : IsCubicallyCofibrant Y) (hX : IsZero X) (f : X ⟶ Y) :
    IsCubicalCofibration f := by
  let e : X ≅ zeroPrespectrum := hX.iso zeroPrespectrum_isZero
  have he : f = e.hom ≫ zeroMap zeroPrespectrum Y := hX.eq_of_src _ _
  rw [he]
  intro E B p hp
  exact IsCubicalCofibration.comp (isCubicalCofibration_of_isIso e.hom) hY p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
