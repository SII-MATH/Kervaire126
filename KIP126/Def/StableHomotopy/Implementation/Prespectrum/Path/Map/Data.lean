module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

/-- Postcompose each retained path with a strict prespectrum map. -/
def pathMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    pathPrespectrum X ⟶ pathPrespectrum Y where
  level n := ⟨fun p => (f.level n).comp p, ContinuousMap.continuous_postcomp (f.level n)⟩
  point n := by
    apply ContinuousMap.ext
    intro s
    exact f.point n
  bond n p t := by
    change C(I, X.level n) at p
    apply ContinuousMap.ext
    intro s
    exact f.bond n (p s) t

/-- The actual pointwise path construction on strict prespectra. -/
def pathFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := pathPrespectrum
  map := pathMap
  map_id _ := rfl
  map_comp _ _ := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
