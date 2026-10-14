module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Functor
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The displayed actual finite power of the localized loop functor. -/
noncomputable def sourceLoopPowerFunctor (k : ℕ) : SourceCategory.{u} ⥤ SourceCategory.{u} where
  obj Z := sourceLocalization.obj (piPrespectrum (fun _ : Fin k => Prespectrum.loop Z.as.obj))
  map f := sourcePiMap (fun _ : Fin k => sourceLoopFunctor.map f)
  map_id Z := by
    rw [sourceLoopFunctor.map_id]
    exact sourcePiMap_id (fun _ : Fin k => Prespectrum.loop Z.as.obj)
  map_comp f g := by
    rw [sourceLoopFunctor.map_comp,sourcePiMap_comp]

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
