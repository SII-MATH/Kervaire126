module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

set_option backward.isDefEq.respectTransparency false

universe u

theorem stableGroupRealize_code (X : Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy X d) : stableGroupRealize X d (stableGroupCode X d x) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    change stableLevelClass X d a.stage
      (((Representative.next^[stableGroupStage d 0]) a).atStableLevel a.stage
        (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega)) = _
    rw [stableLevelClass_atStableLevel]
    exact (a.class_eq_iterate_next _).symm

theorem stableGroupCode_levelClass (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (x : stableLevelGroup X d k) :
    stableGroupCode X d (stableLevelClass X d k x) = (⟦⟨k,x⟩⟧ : stableGroupColimit X d) := by
  induction x using Quotient.inductionOn with
  | h p =>
    exact Representative.groupColimit_atStableLevel
      ⟨stableGroupStage d k,stableGroupDimension d k,stableGroup_degree d k,p⟩ k rfl

theorem stableGroupCode_realize (X : Prespectrum.{u}) (d : ℤ)
    (x : stableGroupColimit X d) : stableGroupCode X d (stableGroupRealize X d x) = x := by
  induction x using DirectLimit.induction with
  | ih k x => exact stableGroupCode_levelClass X d k x

end KIP126.StableHomotopy.Implementation.Prespectrum
