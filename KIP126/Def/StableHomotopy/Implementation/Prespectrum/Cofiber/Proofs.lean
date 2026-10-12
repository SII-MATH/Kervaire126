module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem cofiberProjection_image {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) :
    (cofiberProjection f).level n (f.level n x) = (cofiberLevel f n).point :=
  Quot.sound ⟨⟨x,rfl⟩,⟨(X.level n).point,f.point n⟩⟩

@[simp] theorem cofiberProjection_comp {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    f ≫ cofiberProjection f = zeroMap X (pointSetCofiber f) := by
  apply Hom.ext
  funext n
  exact ContinuousMap.ext (fun x => cofiberProjection_image f n x)

@[simp] theorem coneToCofiber_inl {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (y : Y.level n) :
    (coneToCofiber f).level n (Quot.mk _ (.inl y)) = Quot.mk (CofiberRelation f n) y := rfl

@[simp] theorem coneToCofiber_inr {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (t : I) :
    (coneToCofiber f).level n (Quot.mk _ (.inr (x,t))) = (cofiberLevel f n).point := rfl

@[reassoc] theorem coneInclusion_toCofiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneInclusion f ≫ coneToCofiber f = cofiberProjection f := rfl
end KIP126.StableHomotopy.Implementation.Prespectrum
