module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Hom.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem suspensionLoopUncurry_curry {X Y : Prespectrum.{u}}
    (f : X.suspension ⟶ Y) : suspensionLoopUncurry (suspensionLoopCurry f) = f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro z
  rfl

@[simp] theorem suspensionLoopCurry_uncurry {X Y : Prespectrum.{u}}
    (g : X ⟶ Prespectrum.loop Y) : suspensionLoopCurry (suspensionLoopUncurry g) = g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  rfl

theorem suspensionLoopUncurry_natural_left {X' X Y : Prespectrum.{u}}
    (f : X' ⟶ X) (g : X ⟶ Prespectrum.loop Y) :
    suspensionLoopUncurry (f ≫ g) = suspensionMap f ≫ suspensionLoopUncurry g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro z
  rfl

theorem suspensionLoopCurry_natural_right {X Y Y' : Prespectrum.{u}}
    (f : X.suspension ⟶ Y) (g : Y ⟶ Y') :
    suspensionLoopCurry (f ≫ g) = suspensionLoopCurry f ≫ loopMap g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
