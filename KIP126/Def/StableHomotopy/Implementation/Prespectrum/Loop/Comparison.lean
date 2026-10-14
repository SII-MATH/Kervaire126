module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Stable

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- Actual stable uncurrying, on the originally defined stable quotient. -/
def stableLoopHomotopyMap (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (Prespectrum.loop X) d → StableHomotopy X (d+1) :=
  Quot.map Representative.unloop (fun _ _ h => Representative.unloop_relation h)

/-- The cofinal inverse uses one stabilization before currying. -/
def stableLoopHomotopyInverse (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X (d+1) → StableHomotopy (Prespectrum.loop X) d :=
  Quot.map Representative.loopNext (fun _ _ h => Representative.loopNext_relation h)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
