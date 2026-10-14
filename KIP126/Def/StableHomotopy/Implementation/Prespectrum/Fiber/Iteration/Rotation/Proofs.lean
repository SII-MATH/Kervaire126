module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp, reassoc] theorem fiberRotationComparison_projection {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    fiberRotationComparison f ≫ fiberProjection (fiberConnecting f) = loopMap f := rfl

/-- The auxiliary map of actual fibers is a stable equivalence, because
its strict square has the proved iteration equivalence and the identity. -/
theorem fiberRotationTargetMap_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (fiberRotationTargetMap f) := by
  apply fiberMap_stableEquivalence
  · exact fiberIterationComparison_stableEquivalence f
  · apply (stableEquivalence_iff_source_isIso _).mpr
    rw [sourceLocalization.map_id]
    infer_instance

/-- The explicit rotation composite reverses the source loop and adds
only a constant terminal segment. This fixes the rotation sign geometrically. -/
theorem fiberRotationComparison_target_retraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (fiberRotationComparison f ≫ fiberRotationTargetMap f) ≫
      fiberIterationRetraction (fiberProjection f) = loopAdd (loopInverse X) (zeroMap _ _) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  funext v
  change ((fiberIterationPrefix (fiberProjection f) n
    (1,((fiberRotationComparison f ≫ fiberRotationTargetMap f).level n p))).trans
      (fiberCarriedPath (fiberProjection f) n
        ((fiberRotationComparison f ≫ fiberRotationTargetMap f).level n p).val.1)) v =
    (p.symm.trans (Path.refl (X.level n).point)) v
  simp only [Path.trans_apply]
  split_ifs
  · change p (1 * unitInterval.symm _) = p (unitInterval.symm _)
    rw [one_mul]
  · rfl

theorem source_fiberRotationComparison_target_retraction {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    sourceLocalization.map ((fiberRotationComparison f ≫ fiberRotationTargetMap f) ≫
      fiberIterationRetraction (fiberProjection f)) = sourceLocalization.map (loopInverse X) := by
  rw [fiberRotationComparison_target_retraction]
  exact source_loopAdd_zero _

/-- Every source loop identifies with the actual fiber of the connecting
map. The comparison has the displayed strict projection and needs no
assumption on the original map. -/
theorem fiberRotationComparison_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (fiberRotationComparison f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  haveI : IsIso (sourceLocalization.map (fiberRotationTargetMap f)) :=
    (stableEquivalence_iff_source_isIso _).mp (fiberRotationTargetMap_stableEquivalence f)
  haveI : IsIso (sourceLocalization.map (fiberIterationRetraction (fiberProjection f))) :=
    (stableEquivalence_iff_source_isIso _).mp
      (fiberIterationRetraction_stableEquivalence (fiberProjection f))
  let e : Prespectrum.loop X ≅ Prespectrum.loop X :=
    { hom := loopInverse X
      inv := loopInverse X
      hom_inv_id := loopInverse_twice X
      inv_hom_id := loopInverse_twice X }
  haveI : IsIso (sourceLocalization.map (loopInverse X)) :=
    (inferInstance : IsIso (sourceLocalization.mapIso e).hom)
  haveI : IsIso (sourceLocalization.map (fiberRotationComparison f) ≫
      (sourceLocalization.map (fiberRotationTargetMap f) ≫
        sourceLocalization.map (fiberIterationRetraction (fiberProjection f)))) := by
    rw [← Category.assoc,← Functor.map_comp,← Functor.map_comp,
      source_fiberRotationComparison_target_retraction]
    infer_instance
  exact IsIso.of_isIso_comp_right (sourceLocalization.map (fiberRotationComparison f))
    (sourceLocalization.map (fiberRotationTargetMap f) ≫
      sourceLocalization.map (fiberIterationRetraction (fiberProjection f)))

end KIP126.StableHomotopy.Implementation.Prespectrum
