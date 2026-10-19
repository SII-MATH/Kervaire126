module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual right-spectrum map preserves both grid stages and the
cubical dimension, and acts by its original based smash map. -/
noncomputable def DiagonalGridClass.mapRight {X Y Z : Prespectrum.{0}} {d : ℤ}
    (f : Y ⟶ Z) (a : DiagonalGridClass X Y d) : DiagonalGridClass X Z d where
  left := a.left
  right := a.right
  dimension := a.dimension
  degree := a.degree
  homotopy := (spaceSmashMap (𝟙 (X.level a.left)) f).levelHomotopy
    a.right a.dimension a.homotopy

/-- The same actual map retains the specified equality of grid stages. -/
noncomputable def DiagonalGridDiagonalClass.mapRight {X Y Z : Prespectrum.{0}} {d : ℤ}
    (f : Y ⟶ Z) (a : DiagonalGridDiagonalClass X Y d) :
    DiagonalGridDiagonalClass X Z d := ⟨a.val.mapRight f,a.property⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
