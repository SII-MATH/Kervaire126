module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual grid map induced by a strict map of the right spectrum. -/
noncomputable def diagonalGridStableMap (X : Prespectrum.{0}) {Y Z : Prespectrum.{0}}
    (f : Y ⟶ Z) (d : ℤ) : DiagonalGridStable X Y d → DiagonalGridStable X Z d :=
  Quot.map (DiagonalGridClass.mapRight f) (fun a b h => by
    cases h with
    | horizontal =>
        rw [DiagonalGridClass.mapRight_horizontal]
        exact DiagonalGridRelation.horizontal _
    | vertical =>
        rw [DiagonalGridClass.mapRight_vertical]
        exact DiagonalGridRelation.vertical _)

/-- The actual right-spectrum map also descends to the equal-stage
quotient, using the original pair of grid bonds. -/
noncomputable def diagonalGridDiagonalStableMap (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) :
    DiagonalGridDiagonalStable X Y d → DiagonalGridDiagonalStable X Z d :=
  Quot.map (DiagonalGridDiagonalClass.mapRight f) (fun a b h => by
    cases h with
    | step =>
        rw [DiagonalGridDiagonalClass.mapRight_next]
        exact DiagonalGridDiagonalRelation.step _)

end KIP126.StableHomotopy.Implementation.Prespectrum
