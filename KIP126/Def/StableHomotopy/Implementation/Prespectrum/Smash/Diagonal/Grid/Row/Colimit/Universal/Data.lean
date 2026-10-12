module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual two-index quotient is a cocone on the row diagram. -/
noncomputable def diagonalGridRowCocone (X Y : Prespectrum.{0}) (d : ℤ) :
    Cocone (diagonalGridRowDiagram X Y d) where
  pt := DiagonalGridStable X Y d
  ι := NatTrans.ofSequence
    (fun n => TypeCat.ofHom (diagonalGridRowInclusion X Y d n))
    (fun n => by
      dsimp only [diagonalGridRowDiagram]
      rw [Functor.ofSequence_map_homOfLE_succ]
      ext x
      exact diagonalGridRowInclusion_transition X Y d n x)

/-- The row cocone has the genuine colimit universal property. The
factorizing function evaluates the cocone on the retained row class;
its two quotient checks are the actual vertical and horizontal bonds. -/
noncomputable def diagonalGridRowCocone_isColimit (X Y : Prespectrum.{0}) (d : ℤ) :
    IsColimit (diagonalGridRowCocone X Y d) where
  desc s := TypeCat.ofHom (Quot.lift
    (fun a => s.ι.app a.left a.rowClass)
    (fun a b h => by
      cases h with
      | horizontal =>
          rw [DiagonalGridClass.rowClass_horizontal]
          have h := congrArg (fun k => k a.rowClass) (s.w (homOfLE (Nat.le_succ a.left)))
          dsimp only [diagonalGridRowDiagram] at h
          rw [Functor.ofSequence_map_homOfLE_succ] at h
          exact h.symm
      | vertical => exact congrArg (s.ι.app a.left) a.rowClass_vertical.symm))
  fac s n := by
    ext x
    induction x using Quot.inductionOn with
    | h a =>
        change s.ι.app n (diagonalGridClassOfRowRepresentative X Y d n a).rowClass =
          s.ι.app n (Quot.mk _ a)
        rw [diagonalGridClassOfRowRepresentative_rowClass]
        rfl
  uniq s m h := by
    ext x
    induction x using Quot.inductionOn with
    | h a =>
        have hm := congrArg (fun k => k a.rowClass) (h a.left)
        change m (diagonalGridRowInclusion X Y d a.left a.rowClass) =
          s.ι.app a.left a.rowClass at hm
        rw [a.rowInclusion_rowClass] at hm
        exact hm

end KIP126.StableHomotopy.Implementation.Prespectrum
