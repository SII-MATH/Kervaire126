module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Proofs

@[expose] public section

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
