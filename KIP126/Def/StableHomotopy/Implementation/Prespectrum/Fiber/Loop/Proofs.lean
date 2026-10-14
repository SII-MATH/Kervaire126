module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem fiberLoopToLoopFiber_comp {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberLoopToLoopFiber f ≫ loopFiberToFiberLoop f = 𝟙 (fiber (loopMap f)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Path.ext; rfl
  · apply ContinuousMap.ext; intro s
    apply Path.ext; rfl

@[simp] theorem loopFiberToFiberLoop_comp {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    loopFiberToFiberLoop f ≫ fiberLoopToLoopFiber f = 𝟙 (Prespectrum.loop (fiber f)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext s
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext; intro t; rfl

@[simp, reassoc] theorem fiberLoopToLoopFiber_projection {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    fiberLoopToLoopFiber f ≫ loopMap (fiberProjection f) = fiberProjection (loopMap f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  rfl

@[simp, reassoc] theorem loopFiberToFiberLoop_projection {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    loopFiberToFiberLoop f ≫ fiberProjection (loopMap f) = loopMap (fiberProjection f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
