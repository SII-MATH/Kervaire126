module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Desuspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coneDesuspension_hom_inv {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneDesuspension f ≫ coneDesuspensionInv f = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  cases n with
  | zero =>
    refine Quot.inductionOn z ?_
    rintro (y | ⟨x,t⟩)
    · rfl
    · exact (Quot.sound (ConeRelation.point (f := desuspensionMap f) (n := 0) t)).symm
  | succ n =>
    refine Quot.inductionOn z ?_
    intro z
    rfl

@[simp] theorem coneDesuspension_inv_hom {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneDesuspensionInv f ≫ coneDesuspension f = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  cases n with
  | zero => rfl
  | succ n =>
    refine Quot.inductionOn z ?_
    intro z
    rfl

@[reassoc] theorem coneDesuspension_inclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneInclusion (desuspensionMap f) ≫ coneDesuspension f =
      desuspensionMap (coneInclusion f) := by
  apply Hom.ext
  funext n
  cases n <;> rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
