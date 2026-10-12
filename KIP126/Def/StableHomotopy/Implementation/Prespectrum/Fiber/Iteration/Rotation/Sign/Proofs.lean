module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Actual concatenation on every localized Hom into a loop object agrees
with the already constructed preadditive addition. -/
theorem sourceLoopAdd_eq_add (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f g : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) : sourceLoopAdd X f g = f + g := by
  let P : Fin 2 → Prespectrum.{u} := fun _ => Prespectrum.loop X
  have h : sourcePiLift P (Fin.cases f (fun _ : Fin 1 => g)) =
      sourcePiLift P (Fin.cases f (fun _ : Fin 1 => 0)) +
        sourcePiLift P (Fin.cases 0 (fun _ : Fin 1 => g)) := by
    apply sourcePi_hom_ext P
    intro j
    rw [Preadditive.add_comp,sourcePiLift_projection,sourcePiLift_projection,
      sourcePiLift_projection]
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp
  change sourcePiLift P (Fin.cases f (fun _ : Fin 1 => g)) ≫ _ = f + g
  rw [h,Preadditive.add_comp]
  change sourceLoopAdd X f 0 + sourceLoopAdd X 0 g = f + g
  rw [sourceLoopAdd_zero,zero_sourceLoopAdd]

/-- Actual loop reversal is the additive inverse on every localized Hom. -/
theorem sourceLoopNeg_eq_neg (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) : sourceLoopNeg X f = -f := by
  apply eq_neg_of_add_eq_zero_left
  rw [← sourceLoopAdd_eq_add]
  exact sourceLoopNeg_add X f

/-- The actual loop-reversal map represents the negative identity in the
specified source preadditive structure. -/
theorem source_loopInverse_eq_neg_id (X : Prespectrum.{u}) :
    sourceLocalization.map (loopInverse X) = -𝟙 (sourceLocalization.obj (Prespectrum.loop X)) := by
  simpa only [sourceLoopNeg,Category.id_comp] using sourceLoopNeg_eq_neg X (𝟙 _)

/-- The next connecting map, viewed through the explicit iteration
retraction, is precisely reversal of the original loop map with a constant tail. -/
theorem fiberIterationConnecting_retraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberConnecting (fiberProjection f) ≫ fiberIterationRetraction f =
      loopAdd (loopMap f ≫ loopInverse Y) (zeroMap _ _) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  funext v
  change ((fiberIterationPrefix f n (1,(fiberConnecting (fiberProjection f)).level n p)).trans
    (fiberCarriedPath f n ((fiberConnecting (fiberProjection f)).level n p).val.1)) v =
      (((loopMap f).level n p).symm.trans (Path.refl (Y.level n).point)) v
  simp only [Path.trans_apply]
  split_ifs
  · change f.level n (p (1 * unitInterval.symm _)) = f.level n (p (unitInterval.symm _))
    rw [one_mul]
  · rfl

/-- Rotation of the actual fiber sequence has the required additive negative
loop map, with respect to the proved source preadditive structure. -/
theorem sourceFiberIterationIso_connecting {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map (fiberConnecting (fiberProjection f)) ≫ (sourceFiberIterationIso f).inv =
      -sourceLocalization.map (loopMap f) := by
  change sourceLocalization.map (fiberConnecting (fiberProjection f)) ≫
    sourceLocalization.map (fiberIterationRetraction f) = _
  rw [← Functor.map_comp,fiberIterationConnecting_retraction,source_loopAdd_zero,
    Functor.map_comp,source_loopInverse_eq_neg_id,Preadditive.comp_neg,Category.comp_id]

/-- The comparison used to prove the second rotation equivalence is
the actual negative identity, not an untracked sign convention. -/
theorem source_fiberRotationComparison_target_retraction_eq_neg {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    sourceLocalization.map ((fiberRotationComparison f ≫ fiberRotationTargetMap f) ≫
      fiberIterationRetraction (fiberProjection f)) =
        -𝟙 (sourceLocalization.obj (Prespectrum.loop X)) := by
  rw [source_fiberRotationComparison_target_retraction,source_loopInverse_eq_neg_id]

end KIP126.StableHomotopy.Implementation.Prespectrum
