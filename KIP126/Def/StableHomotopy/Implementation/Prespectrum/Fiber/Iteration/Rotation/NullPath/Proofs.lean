module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.NullPath.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem fiberLoopNullPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberLoopNullPath f ≫ pathEvaluation _ 0 = loopMap f ≫ fiberConnecting f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.source
  · apply ContinuousMap.ext
    intro v
    change f.level n (p (Set.Icc.convexComb 0 1 v)) = f.level n (p v)
    congr 2
    ext
    simp [Set.Icc.convexComb]

@[simp] theorem fiberLoopNullPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberLoopNullPath f ≫ pathEvaluation _ 1 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.target
  · apply ContinuousMap.ext
    intro v
    change f.level n (p (Set.Icc.convexComb 1 1 v)) = (Y.level n).point
    rw [Set.Icc.convexComb_eq,p.target,f.point]

end KIP126.StableHomotopy.Implementation.Prespectrum
