module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Lift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The retained path is a strict nullhomotopy of the fiber composite. -/
def fiberProjectionStrictNullhomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    StrictHomotopy (fiberProjection f ≫ f) (zeroMap (fiber f) Y) where
  hom := fiberNullPath f
  zero := fiberNullPath_zero f
  one := fiberNullPath_one f

/-- Transport the retained fiber nullhomotopy across a specified homotopy
of the square, traversing that square homotopy in reverse first. -/
noncomputable def fiberSquareNullhomotopy {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) :
    StrictHomotopy ((fiberProjection f ≫ a) ≫ g) (zeroMap (fiber f) Y') := by
  let K : StrictHomotopy (fiberProjection f ≫ f ≫ b) (zeroMap (fiber f) Y') :=
    { hom := fiberNullPath f ≫ pathMap b
      zero := by rw [Category.assoc, pathMap_evaluation, ← Category.assoc, fiberNullPath_zero,
        Category.assoc]
      one := by
        rw [Category.assoc, pathMap_evaluation, ← Category.assoc, fiberNullPath_one]
        exact zero_comp }
  exact (StrictHomotopy.precomp (fiberProjection f) H).symm.trans K

/-- An actual homotopy-commuting square induces a strict map of its actual
path fibers, retaining the supplied square homotopy. -/
noncomputable def fiberHomotopyMap {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) : fiber f ⟶ fiber g :=
  fiberLift g (fiberProjection f ≫ a) (fiberSquareNullhomotopy f g a b H).hom
    (fiberSquareNullhomotopy f g a b H).zero (fiberSquareNullhomotopy f g a b H).one

end KIP126.StableHomotopy.Implementation.Prespectrum
