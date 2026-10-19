module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.FiberComparison.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Loop.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology unitInterval
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Retain both original paths in the actual fiber-to-loop-cone map. -/
theorem fiberConeLoop_apply {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : (fiber f).level n) (s : I) :
    (fiberConeLoop f).level n x s =
      if h : (s : ℝ) ≤ 1/2 then
        Quot.mk (ConeRelation f n)
          (.inr (x.val.1,unitInterval.symm
            ⟨2*s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1,h⟩⟩))
      else Quot.mk (ConeRelation f n)
        (.inl (x.val.2 ⟨2*s-1,two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le,s.2.2⟩⟩)) := by
  unfold fiberConeLoop
  exact Path.trans_apply _ _ s

/-- The original cone boundary sends the cone half to the reversed
suspension loop and the retained fiber-path half to the constant loop. -/
theorem fiberConeLoop_boundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberConeLoop f ≫ loopMap (coneBoundary f) =
      loopAdd (fiberProjection f ≫ suspensionLoopCurry (𝟙 X.suspension) ≫
        loopInverse X.suspension) (zeroMap _ _) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change (coneBoundary f).level n ((fiberConeLoop f).level n x s) =
    (((suspensionLoopCurry (𝟙 X.suspension)).level n x.val.1).symm.trans
      (Path.refl (X.suspension.level n).point)) s
  rw [fiberConeLoop_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- After localization the constant half disappears; the formula still
uses the original fiber projection and the original suspension-loop unit. -/
theorem source_fiberConeLoop_boundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map (fiberConeLoop f) ≫ sourceLocalization.map (loopMap (coneBoundary f)) =
      sourceLocalization.map
        (fiberProjection f ≫ suspensionLoopCurry (𝟙 X.suspension) ≫ loopInverse X.suspension) := by
  rw [← sourceLocalization.map_comp, fiberConeLoop_boundary, source_loopAdd_zero]

/-- The actual reverse Puppe loop has the same reversed-boundary formula,
now with the original map in place of the fiber projection. -/
theorem coneIterationLoop_boundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationLoop f ≫ loopMap (coneBoundary (coneInclusion f)) =
      loopAdd (f ≫ suspensionLoopCurry (𝟙 Y.suspension) ≫ loopInverse Y.suspension)
        (zeroMap _ _) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change (coneBoundary (coneInclusion f)).level n ((coneIterationLoop f).level n x s) =
    (((suspensionLoopCurry (𝟙 Y.suspension)).level n (f.level n x)).symm.trans
      (Path.refl (Y.suspension.level n).point)) s
  rw [coneIterationLoop_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem source_coneIterationLoop_boundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map (coneIterationLoop f) ≫
        sourceLocalization.map (loopMap (coneBoundary (coneInclusion f))) =
      sourceLocalization.map (f ≫ suspensionLoopCurry (𝟙 Y.suspension) ≫
        loopInverse Y.suspension) := by
  rw [← sourceLocalization.map_comp, coneIterationLoop_boundary, source_loopAdd_zero]

end KIP126.StableHomotopy.Implementation.Prespectrum
