module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum
public import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual spaces at a fixed level of a sequential diagram of prespectra. -/
def sequentialLevelDiagram (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) : ℕ ⥤ TopCat.{u} where
  obj k := (F.obj k).level n |>.space
  map h := TopCat.ofHom ((F.map h).level n)
  map_id k := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f : F.obj k ⟶ F.obj k => f.level n x) (F.map_id k)
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f.level n x) (F.map_comp h k)

/-- The actual topological colimit level, based at the common image of the
initial stage's basepoint. -/
noncomputable def sequentialColimitLevel (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) : BasedSpace.{u} where
  space := colimit (sequentialLevelDiagram F n)
  point := colimit.ι (sequentialLevelDiagram F n) 0 ((F.obj 0).level n).point

/-- The actual level inclusion into the displayed topological colimit. -/
noncomputable def sequentialColimitLevelInclusion (F : ℕ ⥤ Prespectrum.{u}) (n k : ℕ) :
    C((F.obj k).level n, sequentialColimitLevel F n) :=
  (colimit.ι (sequentialLevelDiagram F n) k).hom

end KIP126.StableHomotopy.Implementation.Prespectrum
