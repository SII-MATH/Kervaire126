module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem fiberIterationMoveHomotopy_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberIterationMoveHomotopy f ≫ pathEvaluation _ 1 =
      fiberIterationRetraction f ≫ fiberIterationComparison f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact z.property.2
    · rfl
  · apply ContinuousMap.ext
    intro v
    change z.val.2 (Set.Icc.convexComb 1 1 v) = (X.level n).point
    rw [Set.Icc.convexComb_eq]
    exact z.property.2

@[simp] theorem fiberIterationPaddingHomotopy_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberIterationPaddingHomotopy f ≫ pathEvaluation _ 1 = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact congrArg (fun q : Path (f.level n z.val.1.val.1) (Y.level n).point => q v)
        (Path.delayReflLeft_one (fiberCarriedPath f n z.val.1))
  · rfl

theorem fiberIterationHomotopy_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberIterationMoveHomotopy f ≫ pathEvaluation _ 0 =
      fiberIterationPaddingHomotopy f ≫ pathEvaluation _ 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact z.property.1
    · apply ContinuousMap.ext
      intro v
      exact (fiberIterationMoveFamily_zero f n z v).trans
        (congrArg (fun q : Path (f.level n z.val.1.val.1) (Y.level n).point => q v)
          (Path.delayReflLeft_zero (fiberCarriedPath f n z.val.1))).symm
  · apply ContinuousMap.ext
    intro v
    change z.val.2 (Set.Icc.convexComb 0 1 v) = z.val.2 v
    congr 1
    ext
    simp [Set.Icc.convexComb]

/-- The other composite inserts just the constant initial loop. -/
theorem fiberIterationComparison_retraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberIterationComparison f ≫ fiberIterationRetraction f =
      loopAdd (zeroMap _ _) (𝟙 (Prespectrum.loop Y)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  funext v
  change ((fiberIterationPrefix f n (1,(fiberIterationComparison f).level n p)).trans
    (fiberCarriedPath f n ((fiberIterationComparison f).level n p).val.1)) v =
      ((Path.refl (Y.level n).point).trans p) v
  simp only [Path.trans_apply]
  split_ifs
  · exact f.point n
  · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
