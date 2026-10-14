module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Lift.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Kernel.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A target loop determines a point of the second actual homotopy fiber,
with constant source null-path. -/
def fiberIterationComparison {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Prespectrum.loop Y ⟶ fiber (fiberProjection f) :=
  fiberLift (fiberProjection f) (fiberConnecting f) (zeroMap _ _) rfl rfl

/-- Reverse an initial segment of the retained source null-path. -/
def fiberIterationPrefix {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : I × (fiber (fiberProjection f)).level n) :
    Path (f.level n (z.2.val.2 z.1)) (f.level n z.2.val.1.val.1) where
  toFun t := f.level n (z.2.val.2 (z.1 * unitInterval.symm t))
  continuous_toFun := (f.level n).continuous.comp (z.2.val.2.continuous.comp
    ((continuous_const.mul unitInterval.continuous_symm.subtype_val).subtype_mk _))
  source' := by simp only [unitInterval.symm_zero,mul_one]
  target' := by
    simp only [unitInterval.symm_one,mul_zero]
    exact congrArg (f.level n) z.2.property.1

/-- Carry the retained target path while the source moves along its null-path. -/
noncomputable def fiberIterationMovePath {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : I × (fiber (fiberProjection f)).level n) :
    Path (f.level n (z.2.val.2 z.1)) (Y.level n).point :=
  (fiberIterationPrefix f n z).trans (fiberCarriedPath f n z.2.val.1)

/-- Jointly continuous family of the transported target paths. -/
noncomputable def fiberIterationMoveFamily {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C((I × (fiber (fiberProjection f)).level n) × I,Y.level n) :=
  ⟨fun z => fiberIterationMovePath f n z.1 z.2,
    Path.trans_continuous_family (fiberIterationPrefix f n) (by
      change Continuous (fun z : (I × (fiber (fiberProjection f)).level n) × I =>
        f.level n (z.1.2.val.2 (z.1.1 * unitInterval.symm z.2)))
      exact (f.level n).continuous.comp
        ((continuous_fst.snd.subtype_val.snd).eval
          ((continuous_fst.fst.subtype_val.mul
            (unitInterval.continuous_symm.comp continuous_snd).subtype_val).subtype_mk _)))
      (fun z => fiberCarriedPath f n z.2.val.1) (by
        change Continuous (fun z : (I × (fiber (fiberProjection f)).level n) × I =>
          z.1.2.val.1.val.2 z.2)
        exact (continuous_fst.snd.subtype_val.fst.subtype_val.snd).eval continuous_snd)⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
