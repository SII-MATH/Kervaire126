module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Representative.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The row inclusion respects both of the original stable generators. -/
theorem diagonalGridClassOfRowRepresentative_relation (X Y : Prespectrum.{0})
    (d : ℤ) (n : ℕ)
    {a b : Representative (spaceSmash (X.level n) Y) (d+n)}
    (h : StableRelation (spaceSmash (X.level n) Y) (d+n) a b) :
    (Quot.mk _ (diagonalGridClassOfRowRepresentative X Y d n a) :
      DiagonalGridStable X Y d) =
      Quot.mk _ (diagonalGridClassOfRowRepresentative X Y d n b) := by
  cases h with
  | homotopy p h =>
      apply congrArg (Quot.mk _)
      unfold diagonalGridClassOfRowRepresentative
      congr 1
      exact Quotient.sound h
  | stabilization => exact Quot.sound (DiagonalGridRelation.vertical _)

@[simp] theorem DiagonalGridClass.rowClass_vertical {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) : a.vertical.rowClass = a.rowClass := by
  rcases a with ⟨n,k,r,h,p⟩
  induction p using Quotient.inductionOn with
  | h p => exact (Quot.sound (StableRelation.stabilization
      ({ stage := k, dimension := r, degree := h, loop := p } :
        Representative (spaceSmash (X.level n) Y) (d+n)))).symm

@[simp] theorem DiagonalGridClass.rowClass_horizontal {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) : a.horizontal.rowClass =
      diagonalGridRowTransition X Y d a.left a.rowClass := by
  rcases a with ⟨n,k,r,h,p⟩
  induction p using Quotient.inductionOn with
  | h p => rfl

@[simp] theorem diagonalGridClassOfRowRepresentative_rowClass
    (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    (diagonalGridClassOfRowRepresentative X Y d n a).rowClass = Quot.mk _ a := by
  cases a
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
