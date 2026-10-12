module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

theorem stableLoopHomotopyMap_inverse (X : Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy X (d+1)) :
    stableLoopHomotopyMap X d (stableLoopHomotopyInverse X d x) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    change Quot.mk _ a.loopNext.unloop = Quot.mk _ a
    rw [Representative.unloop_loopNext]
    exact (Quot.sound (StableRelation.stabilization a)).symm

theorem stableLoopHomotopyInverse_map (X : Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy (Prespectrum.loop X) d) :
    stableLoopHomotopyInverse X d (stableLoopHomotopyMap X d x) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    change Quot.mk _ a.unloop.loopNext = Quot.mk _ a
    rw [Representative.loopNext_unloop]
    exact (Quot.sound (StableRelation.stabilization a)).symm

theorem Representative.unloop_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) {d : ℤ}
    (a : Representative (Prespectrum.loop X) d) :
    (a.map (loopMap f)).unloop = a.unloop.map f := rfl

/-- Uncurrying is natural for actual strict prespectrum maps. -/
theorem stableLoopHomotopyMap_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ)
    (x : StableHomotopy (Prespectrum.loop X) d) :
    stableLoopHomotopyMap Y d (stableHomotopyMap (loopMap f) d x) =
      stableHomotopyMap f (d+1) (stableLoopHomotopyMap X d x) := by
  induction x using Quot.inductionOn with
  | h a => rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
