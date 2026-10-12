module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Contractible.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
universe u

/-- The actual path fiber of the unique map to the point prespectrum
is strictly isomorphic to its domain. -/
def fiberZeroIso (X : Prespectrum.{u}) : fiber (zeroMap X zeroPrespectrum) ≅ X where
  hom := fiberProjection (zeroMap X zeroPrespectrum)
  inv := fiberZeroSection X
  hom_inv_id := fiberZeroProjection_section X
  inv_hom_id := fiberZeroSection_projection X

/-- The standard fiber triangle of the unique map to the point is the
actual contractible source triangle. -/
noncomputable def sourceFiberZeroTriangleIso (X : Prespectrum.{u}) :
    sourceFiberTriangle (zeroMap X zeroPrespectrum) ≅
      contractibleTriangle (sourceLocalization.obj X) :=
  Triangle.isoMk _ _ (sourceLocalization.mapIso (fiberZeroIso X))
    (Iso.refl _) source_zeroPrespectrum_isZero.isoZero
    (by
      change sourceLocalization.map (fiberProjection (zeroMap X zeroPrespectrum)) ≫ 𝟙 _ =
        sourceLocalization.map (fiberProjection (zeroMap X zeroPrespectrum)) ≫ 𝟙 _
      rfl)
    (by
      apply (isZero_zero SourceCategory).eq_of_tgt)
    (by
      apply source_zeroPrespectrum_isZero.eq_of_src)

end KIP126.StableHomotopy.Implementation.Prespectrum
