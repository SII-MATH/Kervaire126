module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Lift.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

@[simp, reassoc] theorem fiberLift_projection {A X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (a : A ⟶ X) (H : A ⟶ pathPrespectrum Y)
    (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f) (h₁ : H ≫ pathEvaluation Y 1 = zeroMap A Y) :
    fiberLift f a H h₀ h₁ ≫ fiberProjection f = a := rfl

@[simp, reassoc] theorem fiberLift_nullPath {A X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (a : A ⟶ X) (H : A ⟶ pathPrespectrum Y)
    (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f) (h₁ : H ≫ pathEvaluation Y 1 = zeroMap A Y) :
    fiberLift f a H h₀ h₁ ≫ fiberNullPath f = H := rfl

/-- The source projection and retained nullhomotopy uniquely specify a
strict map into the actual fiber. -/
theorem fiberHom_ext {A X Y : Prespectrum.{u}} {f : X ⟶ Y}
    (a b : A ⟶ fiber f)
    (hp : a ≫ fiberProjection f = b ≫ fiberProjection f)
    (hH : a ≫ fiberNullPath f = b ≫ fiberNullPath f) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k : A ⟶ X => k.level n x) hp)
    (congrArg (fun k : A ⟶ pathPrespectrum Y => k.level n x) hH)

end KIP126.StableHomotopy.Implementation.Prespectrum
