module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
/-- A strict commuting square induces the literal mapping-cone map,
keeping the original cone parameter. -/
def coneMap {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : cone f ⟶ cone g :=
  coneLift f (b ≫ coneInclusion g) (a ≫ coneNullPath g)
    (by rw [Category.assoc,coneNullPath_zero,← Category.assoc,← h,Category.assoc])
    (by rw [Category.assoc,coneNullPath_one]; rfl)
end KIP126.StableHomotopy.Implementation.Prespectrum
