module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval

/-- The horizontal bond of the actual two-index smash grid. The interval
acts on the first spectrum and the second point is retained. -/
noncomputable def diagonalGridBondLeft (X Y : Prespectrum.{0}) (n k : ℕ) :
    C(((X.level n).smash (Y.level k)) × I, (X.level (n+1)).smash (Y.level k)) :=
  BasedSpace.smashFamily (X.bond n) ContinuousMap.fst (X.bond_point n) (fun _ => rfl)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem diagonalGridBondLeft_apply (X Y : Prespectrum.{0}) (n k : ℕ)
    (x : X.level n) (y : Y.level k) (t : I) :
    diagonalGridBondLeft X Y n k (BasedSpace.smashPoint _ _ x y,t) =
      BasedSpace.smashPoint _ _ (X.bond n (x,t)) y :=
  BasedSpace.smashFamily_apply _ _ _ _ x y t

@[simp] theorem diagonalGridBondLeft_point (X Y : Prespectrum.{0}) (n k : ℕ) (t : I) :
    diagonalGridBondLeft X Y n k (((X.level n).smash (Y.level k)).point,t) =
      ((X.level (n+1)).smash (Y.level k)).point :=
  BasedSpace.smashFamily_point _ _ _ _ t

@[simp] theorem diagonalGridBondLeft_zero (X Y : Prespectrum.{0}) (n k : ℕ)
    (z : (X.level n).smash (Y.level k)) :
    diagonalGridBondLeft X Y n k (z,0) = ((X.level (n+1)).smash (Y.level k)).point := by
  refine Quot.inductionOn z ?_
  rintro ⟨x,y⟩
  change diagonalGridBondLeft X Y n k (BasedSpace.smashPoint _ _ x y,0) = _
  rw [diagonalGridBondLeft_apply,X.bond_zero,BasedSpace.smashPoint_base_left]

@[simp] theorem diagonalGridBondLeft_one (X Y : Prespectrum.{0}) (n k : ℕ)
    (z : (X.level n).smash (Y.level k)) :
    diagonalGridBondLeft X Y n k (z,1) = ((X.level (n+1)).smash (Y.level k)).point := by
  refine Quot.inductionOn z ?_
  rintro ⟨x,y⟩
  change diagonalGridBondLeft X Y n k (BasedSpace.smashPoint _ _ x y,1) = _
  rw [diagonalGridBondLeft_apply,X.bond_one,BasedSpace.smashPoint_base_left]

/-- The two independent bond intervals commute on actual smash points.
The later loop comparison still has to rotate their cubical coordinates. -/
theorem diagonalGridBondLeft_right (X Y : Prespectrum.{0}) (n k : ℕ)
    (z : (X.level n).smash (Y.level k)) (s t : I) :
    diagonalGridBondLeft X Y n (k+1) ((spaceSmash (X.level n) Y).bond k (z,t),s) =
      (spaceSmash (X.level (n+1)) Y).bond k (diagonalGridBondLeft X Y n k (z,s),t) := by
  refine Quot.inductionOn z ?_
  rintro ⟨x,y⟩
  change diagonalGridBondLeft X Y n (k+1)
    (BasedSpace.smashFamily ContinuousMap.fst (Y.bond k) (fun _ => rfl)
      (Y.bond_point k) (BasedSpace.smashPoint _ _ x y,t),s) =
    (spaceSmash (X.level (n+1)) Y).bond k
      (diagonalGridBondLeft X Y n k (BasedSpace.smashPoint _ _ x y,s),t)
  rw [BasedSpace.smashFamily_apply,diagonalGridBondLeft_apply,diagonalGridBondLeft_apply]
  exact (BasedSpace.smashFamily_apply ContinuousMap.fst (Y.bond k)
    (fun _ => rfl) (Y.bond_point k) _ _ _).symm

end KIP126.StableHomotopy.Implementation.Prespectrum

end
