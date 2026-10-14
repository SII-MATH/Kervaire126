module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Kernel.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
  (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point)
  (H : ContinuousMap.HomotopyRel ((fiberProjection f).levelLoop n r p).val
    (ContinuousMap.const _ (X.level n).point) (Cube.boundary (Fin r)))

theorem fiberMoveFamily_side (s : I) (x : Fin r → I)
    (hx : x ∈ Cube.boundary (Fin r)) (v : I) :
    fiberMoveFamily f n r p H ((s,x),v) = (Y.level n).point := by
  change ((fiberMovePrefix f n r p H (s,x)).trans (fiberCarriedPath f n (p x))) v = _
  simp only [Path.trans_apply]
  split_ifs
  · change f.level n (H (_,x)) = _
    rw [H.eq_fst _ hx]
    exact (congrArg (fun z : fiberLevel f n => f.level n z.val.1) (p.property x hx)).trans
      (f.point n)
  · exact congrArg (fun z : fiberLevel f n => z.val.2 _) (p.property x hx)

theorem fiberMoveFamily_zero (x : Fin r → I) (v : I) :
    fiberMoveFamily f n r p H ((0,x),v) =
      ((Path.refl (f.level n (p x).val.1)).trans (fiberCarriedPath f n (p x))) v := by
  change ((fiberMovePrefix f n r p H (0,x)).trans (fiberCarriedPath f n (p x))) v = _
  simp only [Path.trans_apply]
  split_ifs
  · change f.level n (H (0 * _,x)) = _
    rw [zero_mul,H.apply_zero]
    rfl
  · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
