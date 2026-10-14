module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Grid.Inverse.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The actual original even-stage quotient and the signed equal-index
grid quotient are equivalent, with both maps defined on actual representatives. -/
noncomputable def diagonalEvenStableGridEquiv (X Y : Prespectrum.{0}) (d : ℤ) :
    EvenStableHomotopy (diagonalSmash X Y) d ≃ DiagonalGridDiagonalStable X Y d where
  toFun := Quot.lift (fun a => Quot.mk _ (diagonalGridOfEvenRepresentative a))
    (fun _ _ h => diagonalGridOfEvenRepresentative_relation h)
  invFun := Quot.lift diagonalEvenStableOfGridClass
    (fun _ _ h => diagonalEvenStableOfGridClass_relation h)
  left_inv x := by
    induction x using Quot.inductionOn with
    | h a => exact diagonalEvenStableOfGridClass_ofEven a
  right_inv x := by
    induction x using Quot.inductionOn with
    | h a =>
        obtain ⟨a,rfl⟩ := diagonalGridOfEvenRepresentative_surjective X Y d a
        simp only [diagonalEvenStableOfGridClass_ofEven]

/-- The original recursive diagonal stable quotient equals the actual
equal-index grid quotient, with its genuine paired structure maps. -/
noncomputable def diagonalStableHomotopyDiagonalGridEquiv (X Y : Prespectrum.{0}) (d : ℤ) :
    StableHomotopy (diagonalSmash X Y) d ≃ DiagonalGridDiagonalStable X Y d :=
  (evenStableHomotopyEquiv (diagonalSmash X Y) d).symm.trans
    (diagonalEvenStableGridEquiv X Y d)

/-- The original recursive diagonal spectrum has exactly the actual
signed grid's stable homotopy quotient. -/
noncomputable def diagonalStableHomotopyGridEquiv (X Y : Prespectrum.{0}) (d : ℤ) :
    StableHomotopy (diagonalSmash X Y) d ≃ DiagonalGridStable X Y d :=
  (diagonalStableHomotopyDiagonalGridEquiv X Y d).trans
    (diagonalGridStableDiagonalEquiv X Y d).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
