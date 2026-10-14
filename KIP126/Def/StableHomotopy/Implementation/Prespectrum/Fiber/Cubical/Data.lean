module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A based nullhomotopy of the image supplies the actual path coordinate
of a cubical loop in the homotopy fiber. -/
def fiberLiftNullhomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point)
    (H : ContinuousMap.HomotopyRel (f.levelLoop n r p).val (ContinuousMap.const _ (Y.level n).point)
      (Cube.boundary (Fin r))) :
    GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point := by
  let paths : C((Fin r → I), C(I,Y.level n)) :=
    (H.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
  refine ⟨⟨fun x => ⟨(p x,paths x),⟨H.apply_zero x,H.apply_one x⟩⟩,
    (p.val.continuous.prodMk paths.continuous).subtype_mk _⟩,?_⟩
  intro x hx
  apply Subtype.ext
  apply Prod.ext
  · exact p.property x hx
  · apply ContinuousMap.ext
    intro s
    change H (s,x) = (Y.level n).point
    rw [H.eq_fst s hx]
    change f.level n (p x) = _
    exact (congrArg (f.level n) (p.property x hx)).trans (f.point n)

/-- The retained paths give a based cubical nullhomotopy after projection
and application of the original map. -/
def fiberProjectionNullhomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point) :
    ContinuousMap.HomotopyRel
      (f.levelLoop n r ((fiberProjection f).levelLoop n r p)).val (ContinuousMap.const _ (Y.level n).point)
      (Cube.boundary (Fin r)) where
  toFun z := (p z.2).val.2 z.1
  continuous_toFun :=
    ((continuous_subtype_val.snd.comp (p.val.continuous.comp continuous_snd)).eval continuous_fst)
  map_zero_left x := (p x).property.1
  map_one_left x := (p x).property.2
  prop' s x hx := by
    change (p x).val.2 s = f.level n (p x).val.1
    have hp := congrArg (fun z : fiberLevel f n => z.val.2 s) (p.property x hx)
    have hq := congrArg (fun z : fiberLevel f n => f.level n z.val.1) (p.property x hx)
    exact hp.trans (hq.trans (f.point n)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
