module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual retained path is a strict homotopy of the two cospan composites. -/
def homotopyPullbackStrictHomotopy {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    StrictHomotopy (homotopyPullbackFst f g ≫ f) (homotopyPullbackSnd f g ≫ g) where
  hom := homotopyPullbackPath f g
  zero := homotopyPullbackPath_zero f g
  one := homotopyPullbackPath_one f g

/-- The diagonal into the actual path homotopy pullback retains the constant path. -/
def homotopyPullbackDiagonal {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X ⟶ homotopyPullback f f :=
  homotopyPullbackLift (𝟙 X) (𝟙 X) (f ≫ pathConstant Y)
    (by simp) (by simp)

end KIP126.StableHomotopy.Implementation.Prespectrum
