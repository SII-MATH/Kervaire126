module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data

@[expose] public section

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
