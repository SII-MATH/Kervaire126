module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Cubical.Data
public import Mathlib.Topology.Homotopy.HSpaces

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual retained continuous map, bundled with its two endpoints. -/
def fiberCarriedPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) (z : fiberLevel f n) :
    Path (f.level n z.val.1) (Y.level n).point where
  toContinuousMap := z.val.2
  source' := z.property.1
  target' := z.property.2

/-- Reverse the initial segment of a nullhomotopy of the source coordinate. -/
def fiberMovePrefix {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point)
    (H : ContinuousMap.HomotopyRel ((fiberProjection f).levelLoop n r p).val
      (ContinuousMap.const _ (X.level n).point) (Cube.boundary (Fin r)))
    (z : I × (Fin r → I)) : Path (f.level n (H z)) (f.level n (p z.2).val.1) where
  toFun t := f.level n (H (z.1 * unitInterval.symm t,z.2))
  continuous_toFun := (f.level n).continuous.comp (H.continuous.comp
    (((continuous_const.mul unitInterval.continuous_symm.subtype_val).subtype_mk _).prodMk
      continuous_const))
  source' := by simp only [unitInterval.symm_zero,mul_one]
  target' := by
    simp only [unitInterval.symm_one,mul_zero,H.apply_zero]
    rfl

/-- Attach the reversed initial nullhomotopy segment to the retained path. -/
noncomputable def fiberMovePath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point)
    (H : ContinuousMap.HomotopyRel ((fiberProjection f).levelLoop n r p).val
      (ContinuousMap.const _ (X.level n).point) (Cube.boundary (Fin r)))
    (z : I × (Fin r → I)) : Path (f.level n (H z)) (Y.level n).point :=
  (fiberMovePrefix f n r p H z).trans (fiberCarriedPath f n (p z.2))

/-- Joint continuity of the transported paths, including the loop parameter. -/
noncomputable def fiberMoveFamily {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point)
    (H : ContinuousMap.HomotopyRel ((fiberProjection f).levelLoop n r p).val
      (ContinuousMap.const _ (X.level n).point) (Cube.boundary (Fin r))) :
    C((I × (Fin r → I)) × I,Y.level n) :=
  ⟨fun z => fiberMovePath f n r p H z.1 z.2,
    Path.trans_continuous_family (fiberMovePrefix f n r p H) (by
      change Continuous (fun z : (I × (Fin r → I)) × I =>
        f.level n (H (z.1.1 * unitInterval.symm z.2,z.1.2)))
      exact (f.level n).continuous.comp (H.continuous.comp
        (((continuous_fst.fst.subtype_val.mul
          (unitInterval.continuous_symm.comp continuous_snd).subtype_val).subtype_mk _).prodMk
          continuous_fst.snd)))
      (fun z => fiberCarriedPath f n (p z.2)) (by
        change Continuous (fun z : (I × (Fin r → I)) × I => (p z.1.2).val.2 z.2)
        exact ((continuous_subtype_val.snd.comp (p.val.continuous.comp continuous_fst.snd)).eval
          continuous_snd))⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
