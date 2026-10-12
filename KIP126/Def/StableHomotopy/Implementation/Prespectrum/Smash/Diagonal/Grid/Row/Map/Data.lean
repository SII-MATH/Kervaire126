module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual natural transformation on the row diagrams induced by
a strict map of the right spectrum. -/
noncomputable def diagonalGridRowMap (X : Prespectrum.{0}) {Y Z : Prespectrum.{0}}
    (f : Y ⟶ Z) (d : ℤ) : diagonalGridRowDiagram X Y d ⟶ diagonalGridRowDiagram X Z d :=
  NatTrans.ofSequence
    (fun n => TypeCat.ofHom (stableHomotopyMap (spaceSmashMap (𝟙 (X.level n)) f) (d+n)))
    (fun n => by
      dsimp only [diagonalGridRowDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ,Functor.ofSequence_map_homOfLE_succ]
      ext x
      exact diagonalGridRowTransition_natural_right X f d n x)

end KIP126.StableHomotopy.Implementation.Prespectrum
