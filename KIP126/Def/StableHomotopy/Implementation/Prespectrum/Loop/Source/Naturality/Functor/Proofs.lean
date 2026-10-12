module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Naturality.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceLoopPowerFunctor_map (k : ℕ) {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (sourceLoopPowerFunctor k).map (sourceLocalization.map f) =
      sourceLocalization.map (piMap (fun _ : Fin k => loopMap f)) := by
  change sourcePiMap (fun _ : Fin k => sourceLoopFunctor.map (sourceLocalization.map f)) = _
  rw [sourceLoopFunctor_map,sourcePiMap_map]

end KIP126.StableHomotopy.Implementation.Prespectrum
