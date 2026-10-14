module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Fiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

@[simp, reassoc] theorem fiberToHomotopyPullback_fst {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberToHomotopyPullback f ≫ homotopyPullbackFst f (zeroMap zeroPrespectrum Y) =
      fiberProjection f := rfl

@[simp, reassoc] theorem fiberToHomotopyPullback_path {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberToHomotopyPullback f ≫ homotopyPullbackPath f (zeroMap zeroPrespectrum Y) =
      fiberNullPath f := rfl

@[simp, reassoc] theorem homotopyPullbackToFiber_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyPullbackToFiber f ≫ fiberProjection f =
      homotopyPullbackFst f (zeroMap zeroPrespectrum Y) := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
