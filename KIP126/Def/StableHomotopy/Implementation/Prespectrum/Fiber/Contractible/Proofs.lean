module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Contractible.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem fiberZeroSection_projection (X : Prespectrum.{u}) :
    fiberZeroSection X ≫ fiberProjection (zeroMap X zeroPrespectrum) = 𝟙 X := rfl

@[simp] theorem fiberZeroProjection_section (X : Prespectrum.{u}) :
    fiberProjection (zeroMap X zeroPrespectrum) ≫ fiberZeroSection X =
      𝟙 (fiber (zeroMap X zeroPrespectrum)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change (PUnit.unit : PUnit.{u+1}) = z.val.2 t
    exact Subsingleton.elim _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
