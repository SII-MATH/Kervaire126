module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Universal.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual strict square induces its ordinary quotient map. -/
def cofiberMap {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : pointSetCofiber f ⟶ pointSetCofiber g :=
  cofiberDesc f (b ≫ cofiberProjection g) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    change (cofiberProjection g).level n (b.level n (f.level n x)) = _
    rw [show b.level n (f.level n x) = g.level n (a.level n x) from
      congrArg (fun e : X ⟶ Y' => e.level n x) h,cofiberProjection_image]
    rfl)
end KIP126.StableHomotopy.Implementation.Prespectrum
