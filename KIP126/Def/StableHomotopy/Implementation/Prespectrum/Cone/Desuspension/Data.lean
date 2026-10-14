module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Tail.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual literal cone commutes with padding by the based one-point
level; the padded cone level is collapsed to that one point. -/
def coneDesuspension {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    cone (desuspensionMap f) ⟶ (cone f).desuspension where
  level
    | 0 => ContinuousMap.const _ ((cone f).desuspension.level 0).point
    | n+1 => ⟨Quot.map id (by
        intro a b h
        cases h with
        | start x => exact ConeRelation.start (f := f) (n := n) x
        | finish x => exact ConeRelation.finish (f := f) (n := n) x
        | point t => exact ConeRelation.point (f := f) (n := n) t), by
        apply continuous_quot_lift
        exact continuous_quot_mk⟩
  point n := by cases n <;> rfl
  bond n x t := by
    cases n with
    | zero =>
      refine Quot.inductionOn x ?_
      rintro (y | ⟨x,s⟩)
      · rfl
      · exact Quot.sound (ConeRelation.point s)
    | succ n =>
      refine Quot.inductionOn x ?_
      rintro (y | ⟨x,s⟩) <;> rfl

/-- The inverse uses the same raw quotient representatives in positive
levels and the cone's actual basepoint in the padded level. -/
def coneDesuspensionInv {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (cone f).desuspension ⟶ cone (desuspensionMap f) where
  level
    | 0 => ContinuousMap.const _ ((cone (desuspensionMap f)).level 0).point
    | n+1 => ⟨Quot.map id (by
        intro a b h
        cases h with
        | start x => exact ConeRelation.start (f := desuspensionMap f) (n := n+1) x
        | finish x => exact ConeRelation.finish (f := desuspensionMap f) (n := n+1) x
        | point t => exact ConeRelation.point (f := desuspensionMap f) (n := n+1) t), by
        apply continuous_quot_lift
        exact continuous_quot_mk⟩
  point n := by cases n <;> rfl
  bond n x t := by
    cases n with
    | zero => rfl
    | succ n =>
      refine Quot.inductionOn x ?_
      rintro (y | ⟨x,s⟩) <;> rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
