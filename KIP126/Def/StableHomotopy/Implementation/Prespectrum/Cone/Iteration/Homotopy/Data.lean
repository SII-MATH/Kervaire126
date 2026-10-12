module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual twice-iterated cone contracts onto the image of the
suspension comparison inverse, through strict based prespectrum maps. -/
noncomputable def coneIterationHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    StrictHomotopy (𝟙 (cone (coneInclusion f)))
      (coneIterationComparison f ≫ coneIterationInverse f) := by
  let inner := coneLift f (coneNullPath (coneInclusion f)) (coneIterationSquare f)
    (coneIterationSquare_zero f) (coneIterationSquare_one f)
  let H := coneLift (coneInclusion f) inner (coneIterationOuterSquare f)
    (by rw [coneIterationOuterSquare_zero]; rfl) (coneIterationOuterSquare_one f)
  refine { hom := H, zero := ?_, one := ?_ }
  · apply Hom.ext; funext n
    apply ContinuousMap.ext; intro z
    refine Quot.inductionOn z ?_
    rintro (w | ⟨y,s⟩)
    · refine Quot.inductionOn w ?_
      rintro (y | ⟨x,s⟩)
      · exact Quot.sound (ConeRelation.start y)
      · exact coneIterationLoop_parameter_zero f n x s
    · change Quot.mk (ConeRelation (coneInclusion f) n)
        (.inr (y,unitInterval.symm (unitInterval.symm s * unitInterval.symm 0))) =
          Quot.mk (ConeRelation (coneInclusion f) n) (.inr (y,s))
      simp
  · apply Hom.ext; funext n
    apply ContinuousMap.ext; intro z
    refine Quot.inductionOn z ?_
    rintro (w | ⟨y,s⟩)
    · refine Quot.inductionOn w ?_
      rintro (y | ⟨x,s⟩)
      · exact (Quot.sound (ConeRelation.finish y)).trans
          ((coneIterationInverse f).point n).symm
      · change (coneIterationLoop f).level n x (coneIterationParameter s 1) =
          (coneIterationLoop f).level n x s
        rw [coneIterationParameter_one]
    · change Quot.mk (ConeRelation (coneInclusion f) n)
        (.inr (y,unitInterval.symm (unitInterval.symm s * unitInterval.symm 1))) =
          (coneIterationInverse f).level n (X.suspension.level n).point
      simp only [unitInterval.symm_one,mul_zero,unitInterval.symm_zero]
      exact (Quot.sound (ConeRelation.finish y)).trans
        ((coneIterationInverse f).point n).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
