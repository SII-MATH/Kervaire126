module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Retain the actual path in the mapping-path total space as a strict
map to the path prespectrum. -/
def mappingPathRetainedPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPath f ⟶ pathPrespectrum Y where
  level n := ⟨fun z => z.val.2,continuous_subtype_val.snd⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- The retained path is a genuine strict homotopy from the source map
to the endpoint projection of its actual mapping-path factorization. -/
def mappingPathRetainedHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    StrictHomotopy (mappingPathRetraction f ≫ f) (mappingPathProjection f) where
  hom := mappingPathRetainedPath f
  zero := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    exact z.property
  one := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
