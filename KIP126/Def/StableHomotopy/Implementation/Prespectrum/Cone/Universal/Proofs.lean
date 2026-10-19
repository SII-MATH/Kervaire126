module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coneNullPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneNullPath f ≫ pathEvaluation (cone f) 0 = f ≫ coneInclusion f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Quot.sound (ConeRelation.start x)

@[simp] theorem coneNullPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneNullPath f ≫ pathEvaluation (cone f) 1 = zeroMap X (cone f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Quot.sound (ConeRelation.finish x)

@[reassoc] theorem coneInclusion_lift {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (a : Y ⟶ Z)
    (H : X ⟶ pathPrespectrum Z) (h₀ : H ≫ pathEvaluation Z 0 = f ≫ a)
    (h₁ : H ≫ pathEvaluation Z 1 = zeroMap X Z) :
    coneInclusion f ≫ coneLift f a H h₀ h₁ = a := rfl

@[reassoc] theorem coneNullPath_lift {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (a : Y ⟶ Z)
    (H : X ⟶ pathPrespectrum Z) (h₀ : H ≫ pathEvaluation Z 0 = f ≫ a)
    (h₁ : H ≫ pathEvaluation Z 1 = zeroMap X Z) :
    coneNullPath f ≫ pathMap (coneLift f a H h₀ h₁) = H := rfl

/-- These two actual pieces determine a strict map out of the original
mapping cone; its retained nullhomotopy is part of the universal data. -/
theorem coneHom_ext {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) {a b : cone f ⟶ Z}
    (h : coneInclusion f ≫ a = coneInclusion f ≫ b)
    (k : coneNullPath f ≫ pathMap a = coneNullPath f ≫ pathMap b) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · exact congrArg (fun e : Y ⟶ Z => e.level n y) h
  · exact congrArg (fun e : X ⟶ pathPrespectrum Z =>
      (show C(I,Z.level n) from e.level n x) t) k

end KIP126.StableHomotopy.Implementation.Prespectrum
