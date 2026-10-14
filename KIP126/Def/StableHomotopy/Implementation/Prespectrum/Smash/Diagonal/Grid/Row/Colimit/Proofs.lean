module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- A row inclusion identifies its two actual horizontal stages. -/
theorem diagonalGridRowInclusion_transition (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    (a : StableHomotopy (spaceSmash (X.level n) Y) (d+n)) :
    diagonalGridRowInclusion X Y d (n+1) (diagonalGridRowTransition X Y d n a) =
      diagonalGridRowInclusion X Y d n a := by
  induction a using Quot.inductionOn with
  | h a => exact (Quot.sound (DiagonalGridRelation.horizontal
      (diagonalGridClassOfRowRepresentative X Y d n a))).symm

@[simp] theorem DiagonalGridClass.rowInclusion_rowClass {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) :
    diagonalGridRowInclusion X Y d a.left a.rowClass = Quot.mk _ a := by
  rcases a with ⟨n,k,r,h,p⟩
  induction p using Quotient.inductionOn with
  | h p => rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
