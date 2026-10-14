module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

/-- The signed horizontal transition commutes with every actual map of
the right spectrum, on the original cubical representatives. -/
theorem diagonalGridLoopHorizontal_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (n k r : ℕ)
    (p : GenLoop (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point) :
    (spaceSmashMap (𝟙 (X.level (n+1))) f).levelLoop k (r+1)
        (diagonalGridLoopHorizontal X Y n k r p) =
      diagonalGridLoopHorizontal X Z n k r
        ((spaceSmashMap (𝟙 (X.level n)) f).levelLoop k r p) := by
  apply GenLoop.ext
  intro t
  change (spaceSmashMap (𝟙 (X.level (n+1))) f).level k
    (diagonalGridBondLeft X Y n k
      (p (fun i => t i.succ),suspensionDesuspensionSign (n+k) (t 0))) =
    diagonalGridBondLeft X Z n k
      ((spaceSmashMap (𝟙 (X.level n)) f).level k (p (fun i => t i.succ)),
        suspensionDesuspensionSign (n+k) (t 0))
  generalize p (fun i => t i.succ) = z
  refine Quot.inductionOn z ?_
  rintro ⟨x,y⟩
  change (spaceSmashMap (𝟙 (X.level (n+1))) f).level k
    (diagonalGridBondLeft X Y n k
      (BasedSpace.smashPoint _ _ x y,suspensionDesuspensionSign (n+k) (t 0))) =
    diagonalGridBondLeft X Z n k
      ((spaceSmashMap (𝟙 (X.level n)) f).level k (BasedSpace.smashPoint _ _ x y),
        suspensionDesuspensionSign (n+k) (t 0))
  rw [diagonalGridBondLeft_apply,spaceSmashMap_apply,spaceSmashMap_apply,
    diagonalGridBondLeft_apply]
  rfl

/-- The horizontal map of original stable representatives is natural
before passing to either stable quotient. -/
theorem diagonalGridRowRepresentative_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    (diagonalGridRowRepresentative X Y d n a).map
        (spaceSmashMap (𝟙 (X.level (n+1))) f) =
      diagonalGridRowRepresentative X Z d n
        (a.map (spaceSmashMap (𝟙 (X.level n)) f)) := by
  rcases a with ⟨k,r,h,p⟩
  unfold Representative.map diagonalGridRowRepresentative
  congr 1
  exact diagonalGridLoopHorizontal_natural_right X f n k r p

/-- The actual right-spectrum map commutes with the descended row maps. -/
theorem diagonalGridRowTransition_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ) (n : ℕ)
    (x : StableHomotopy (spaceSmash (X.level n) Y) (d+n)) :
    stableHomotopyMap (spaceSmashMap (𝟙 (X.level (n+1))) f) (d+(n+1))
        (diagonalGridRowTransition X Y d n x) =
      diagonalGridRowTransition X Z d n
        (stableHomotopyMap (spaceSmashMap (𝟙 (X.level n)) f) (d+n) x) := by
  induction x using Quot.inductionOn with
  | h a =>
      exact congrArg (Quot.mk _) (diagonalGridRowRepresentative_natural_right X f d n a)

end KIP126.StableHomotopy.Implementation.Prespectrum
