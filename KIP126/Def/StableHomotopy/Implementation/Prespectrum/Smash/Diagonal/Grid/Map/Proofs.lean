module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Representative.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory _root_.Topology
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Prespectrum.{0}} {d : ℤ}

@[simp] theorem DiagonalGridClass.mapRight_horizontal (f : Y ⟶ Z)
    (a : DiagonalGridClass X Y d) :
    a.horizontal.mapRight f = (a.mapRight f).horizontal := by
  rcases a with ⟨n,k,r,h,q⟩
  unfold DiagonalGridClass.mapRight DiagonalGridClass.horizontal
  congr 1
  induction q using Quotient.inductionOn with
  | h p => exact congrArg Quotient.mk' (diagonalGridLoopHorizontal_natural_right X f n k r p)

@[simp] theorem DiagonalGridClass.mapRight_vertical (f : Y ⟶ Z)
    (a : DiagonalGridClass X Y d) :
    a.vertical.mapRight f = (a.mapRight f).vertical := by
  rcases a with ⟨n,k,r,h,q⟩
  unfold DiagonalGridClass.mapRight DiagonalGridClass.vertical
  congr 1
  induction q using Quotient.inductionOn with
  | h p =>
      apply congrArg Quotient.mk'
      apply GenLoop.ext
      intro t
      exact (spaceSmashMap (𝟙 (X.level n)) f).bond k _ _

/-- Right-spectrum maps preserve the original representative of each row. -/
theorem diagonalGridClassOfRowRepresentative_mapRight (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    (diagonalGridClassOfRowRepresentative X Y d n a).mapRight f =
      diagonalGridClassOfRowRepresentative X Z d n
        (a.map (spaceSmashMap (𝟙 (X.level n)) f)) := rfl

@[simp] theorem DiagonalGridClass.mapRight_normalize (f : Y ⟶ Z)
    (a : DiagonalGridClass X Y d) : a.normalize.mapRight f = (a.mapRight f).normalize := by
  have hH : Function.Semiconj (@DiagonalGridClass.mapRight X Y Z d f)
      DiagonalGridClass.horizontal DiagonalGridClass.horizontal := mapRight_horizontal f
  have hV : Function.Semiconj (@DiagonalGridClass.mapRight X Y Z d f)
      DiagonalGridClass.vertical DiagonalGridClass.vertical := mapRight_vertical f
  dsimp only [DiagonalGridClass.normalize]
  rw [hH.iterate_right a.right,hV.iterate_right a.left]
  rfl

@[simp] theorem DiagonalGridDiagonalClass.mapRight_next (f : Y ⟶ Z)
    (a : DiagonalGridDiagonalClass X Y d) :
    a.next.mapRight f = (a.mapRight f).next := by
  apply Subtype.ext
  exact (a.val.horizontal.mapRight_vertical f).trans
    (congrArg DiagonalGridClass.vertical (a.val.mapRight_horizontal f))

@[simp] theorem DiagonalGridClass.mapRight_toDiagonal (f : Y ⟶ Z)
    (a : DiagonalGridClass X Y d) :
    a.toDiagonal.mapRight f = (a.mapRight f).toDiagonal :=
  Subtype.ext (a.mapRight_normalize f)

end KIP126.StableHomotopy.Implementation.Prespectrum
