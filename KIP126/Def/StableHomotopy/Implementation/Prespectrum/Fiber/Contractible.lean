module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

/-- The constant retained path gives a strict section of the fiber
projection for the unique map to the point prespectrum. -/
def fiberZeroSection (X : Prespectrum.{u}) : X ⟶ fiber (zeroMap X zeroPrespectrum) where
  level n :=
    { toFun x := ⟨(x,ContinuousMap.const _ PUnit.unit),⟨rfl,rfl⟩⟩
      continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _ }
  point _ := rfl
  bond _ _ _ := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
