module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp, reassoc] theorem fiberIterationComparison_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberIterationComparison f ≫ fiberProjection (fiberProjection f) = fiberConnecting f := rfl

theorem fiberIterationMoveFamily_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : (fiber (fiberProjection f)).level n) (v : I) :
    fiberIterationMoveFamily f n ((0,z),v) =
      ((Path.refl (f.level n z.val.1.val.1)).trans (fiberCarriedPath f n z.val.1)) v := by
  change ((fiberIterationPrefix f n (0,z)).trans (fiberCarriedPath f n z.val.1)) v = _
  simp only [Path.trans_apply]
  split_ifs
  · change f.level n (z.val.2 (0 * _)) = _
    rw [zero_mul,z.property.1]
    rfl
  · rfl

theorem fiberIterationMoveFamily_point {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (s v : I) :
    fiberIterationMoveFamily f n ((s,((fiber (fiberProjection f)).level n).point),v) =
      (Y.level n).point := by
  change ((fiberIterationPrefix f n _).trans (fiberCarriedPath f n _)) v = _
  simp only [Path.trans_apply]
  split_ifs
  · exact f.point n
  · rfl

theorem fiberIterationMoveFamily_bond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : (fiber (fiberProjection f)).level n) (t s v : I) :
    fiberIterationMoveFamily f (n+1) ((s,(fiber (fiberProjection f)).bond n (z,t)),v) =
      Y.bond n (fiberIterationMoveFamily f n ((s,z),v),t) := by
  change ((fiberIterationPrefix f (n+1) _).trans (fiberCarriedPath f (n+1) _)) v =
    Y.bond n (((fiberIterationPrefix f n _).trans (fiberCarriedPath f n _)) v,t)
  simp only [Path.trans_apply]
  split_ifs
  · exact f.bond n _ t
  · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
