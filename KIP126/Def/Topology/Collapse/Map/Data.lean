module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

namespace KIP126.Topology

/-- The original continuous map descends when the inverse image of the
collapsed target subset is collapsed in its source. -/
def collapsePreimageMap {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (S : Set Y) :
    C(Quot (fun a b : E => f a ∈ S ∧ f b ∈ S),
      Quot (fun a b : Y => a ∈ S ∧ b ∈ S)) :=
  ⟨Quot.lift (fun x => Quot.mk _ (f x)) (fun _ _ h => Quot.sound h),
    continuous_quot_lift _ (continuous_quot_mk.comp f.continuous)⟩

end KIP126.Topology
