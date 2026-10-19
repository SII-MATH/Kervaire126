module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Representative
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual horizontal transition after taking vertical stable
homotopy. Its definition descends the signed cubical map, using the
proved square-rotation compatibility with vertical stabilization. -/
noncomputable def diagonalGridRowTransition (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ) :
    StableHomotopy (spaceSmash (X.level n) Y) (d+n) →
      StableHomotopy (spaceSmash (X.level (n+1)) Y) (d+(n+1)) :=
  Quot.lift (fun a => Quot.mk _ (diagonalGridRowRepresentative X Y d n a))
    (fun _ _ h => diagonalGridRowRepresentative_relation X Y d n h)

/-- The genuine row diagram of original stable homotopy sets. The
horizontal maps are defined by actual signed bonds, without positing
strict maps between the underlying row prespectra. -/
noncomputable def diagonalGridRowDiagram (X Y : Prespectrum.{0}) (d : ℤ) : ℕ ⥤ Type :=
  Functor.ofSequence (fun n => TypeCat.ofHom (diagonalGridRowTransition X Y d n))

end KIP126.StableHomotopy.Implementation.Prespectrum
