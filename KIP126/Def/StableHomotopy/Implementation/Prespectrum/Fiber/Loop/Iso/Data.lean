module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Loop.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Transposing the actual loop and null-path parameters gives a strict
isomorphism between the fiber of the loop map and the loop of the fiber. -/
def fiberLoopIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber (loopMap f) ≅ Prespectrum.loop (fiber f) where
  hom := fiberLoopToLoopFiber f
  inv := loopFiberToFiberLoop f
  hom_inv_id := fiberLoopToLoopFiber_comp f
  inv_hom_id := loopFiberToFiberLoop_comp f

end KIP126.StableHomotopy.Implementation.Prespectrum
