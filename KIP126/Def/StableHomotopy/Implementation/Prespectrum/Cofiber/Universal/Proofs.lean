module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Universal.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[reassoc] theorem cofiberProjection_desc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (h : f ≫ a = zeroMap X Z) :
    cofiberProjection f ≫ cofiberDesc f a h = a := rfl

theorem cofiberHom_ext {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    {a b : pointSetCofiber f ⟶ Z} (h : cofiberProjection f ≫ a = cofiberProjection f ≫ b) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro y
  exact congrArg (fun e : Y ⟶ Z => e.level n y) h

@[simp] theorem cofiberDesc_eta {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : pointSetCofiber f ⟶ Z) (h : f ≫ (cofiberProjection f ≫ a) = zeroMap X Z) :
    cofiberDesc f (cofiberProjection f ≫ a) h = a := by
  apply cofiberHom_ext f
  exact cofiberProjection_desc f _ h
end KIP126.StableHomotopy.Implementation.Prespectrum
