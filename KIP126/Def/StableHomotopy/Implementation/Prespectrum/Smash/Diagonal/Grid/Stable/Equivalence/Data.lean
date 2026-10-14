module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- Explicit diagonal cofinality for the actual signed grid. Both
directions descend the original class constructions; normalization
advances `(n,k)` to `(n+k,n+k)` and respects either generating relation. -/
noncomputable def diagonalGridStableDiagonalEquiv (X Y : Prespectrum.{0}) (d : ℤ) :
    DiagonalGridStable X Y d ≃ DiagonalGridDiagonalStable X Y d where
  toFun := Quot.lift (fun a => Quot.mk _ a.toDiagonal) (fun a b h => by
    cases h with
    | horizontal =>
        rw [DiagonalGridClass.toDiagonal_horizontal]
        exact Quot.sound (DiagonalGridDiagonalRelation.step _)
    | vertical =>
        rw [DiagonalGridClass.toDiagonal_vertical]
        exact Quot.sound (DiagonalGridDiagonalRelation.step _))
  invFun := Quot.lift (fun a => Quot.mk _ a.val) (fun a b h => by
    cases h with
    | step =>
        exact (Quot.sound (DiagonalGridRelation.horizontal a.val)).trans
          (Quot.sound (DiagonalGridRelation.vertical a.val.horizontal)))
  left_inv x := by
    induction x using Quot.inductionOn with
    | h a => exact a.stable_eq_normalize.symm
  right_inv x := by
    induction x using Quot.inductionOn with
    | h a =>
        change Quot.mk _ a.val.toDiagonal = Quot.mk _ a
        rw [a.toDiagonal_eq_iterate]
        exact (a.stable_eq_iterate a.val.left).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
