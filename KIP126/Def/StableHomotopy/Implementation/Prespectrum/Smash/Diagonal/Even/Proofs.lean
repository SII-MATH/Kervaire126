module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Bond
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The even levels of the original recursive diagonal construction are
the actual equal-index smash spaces. -/
theorem diagonalLevel_even (X Y : Prespectrum.{0}) (n : ℕ) :
    diagonalLevel X Y (n+n) = (X.level n).smash (Y.level n) := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
      rw [show n+1+(n+1) = n+n+2 by omega]
      change diagonalLevel X.tail Y.tail (n+n) = _
      rw [ih]
      rfl

/-- The intervening odd level is exactly the suspension of that smash. -/
theorem diagonalLevel_odd (X Y : Prespectrum.{0}) (n : ℕ) :
    diagonalLevel X Y (n+n+1) = ((X.level n).smash (Y.level n)).suspension := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
      rw [show n+1+(n+1)+1 = (n+n+1)+2 by omega]
      change diagonalLevel X.tail Y.tail (n+n+1) = _
      rw [ih]
      rfl

/-- The alternating orientation is the identity on the actual diagonal. -/
@[simp] theorem suspensionDesuspensionSign_double (n : ℕ) (t : I) :
    suspensionDesuspensionSign (n+n) t = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n+1+(n+1) = n+n+1+1 by omega,
        suspensionDesuspensionSign_succ,suspensionDesuspensionSign_succ,
        unitInterval.symm_symm,ih]

/-- Before inserting the alternating grid sign, the two consecutive
original diagonal bonds are exactly the left-then-right grid bonds.
Heterogeneous equality retains the original recursively indexed levels. -/
theorem diagonalBond_pair_heq (X Y : Prespectrum.{0}) (n : ℕ) :
    HEq (fun (z : diagonalLevel X Y (n+n)) (s t : I) =>
      diagonalBond X Y (n+n+1) (diagonalBond X Y (n+n) (z,s),t))
      (fun (z : (X.level n).smash (Y.level n)) (s t : I) =>
        (spaceSmash (X.level (n+1)) Y).bond n (diagonalGridBondLeft X Y n n (z,s),t)) := by
  induction n generalizing X Y with
  | zero =>
      apply heq_of_eq
      funext z s t
      refine Quot.inductionOn z ?_
      rintro ⟨x,y⟩
      change pairedBond X Y (BasedSpace.suspensionProjection _
        (BasedSpace.smashPoint _ _ x y,s),t) =
        (spaceSmash (X.level 1) Y).bond 0
          (diagonalGridBondLeft X Y 0 0 (BasedSpace.smashPoint _ _ x y,s),t)
      apply Eq.trans ((pairedBond_exists X Y).exists.choose_spec.1 x y s t)
      rw [diagonalGridBondLeft_apply]
      exact (BasedSpace.smashFamily_apply ContinuousMap.fst (Y.bond 0)
        (fun _ => rfl) (Y.bond_point 0) _ _ _).symm
  | succ n ih =>
      rw [show n+1+(n+1) = n+n+2 by omega]
      exact ih X.tail Y.tail

end KIP126.StableHomotopy.Implementation.Prespectrum
