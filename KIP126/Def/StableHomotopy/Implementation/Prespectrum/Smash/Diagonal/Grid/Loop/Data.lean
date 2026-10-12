module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Bond
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

/-- The horizontal actual cubical transition, with its alternating
orientation. On the diagonal the sign has even exponent. -/
noncomputable def diagonalGridLoopHorizontal (X Y : Prespectrum.{0}) (n k r : ℕ)
    (p : GenLoop (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point) :
    GenLoop (Fin (r+1)) ((X.level (n+1)).smash (Y.level k))
      ((X.level (n+1)).smash (Y.level k)).point := by
  refine ⟨⟨fun t => diagonalGridBondLeft X Y n k
    (p (fun i => t i.succ),suspensionDesuspensionSign (n+k) (t 0)), ?_⟩, ?_⟩
  · exact (diagonalGridBondLeft X Y n k).continuous.comp
      ((p.val.continuous.comp (continuous_pi fun i => continuous_apply i.succ)).prodMk
        ((suspensionDesuspensionSign (n+k)).continuous.comp (continuous_apply 0)))
  · intro t ht
    change diagonalGridBondLeft X Y n k
      (p (fun i => t i.succ),suspensionDesuspensionSign (n+k) (t 0)) = _
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
        rcases suspensionDesuspensionSign_boundary (n+k) (t 0) hi with h | h
        · rw [h,diagonalGridBondLeft_zero]
        · rw [h,diagonalGridBondLeft_one]
    | succ i =>
        have hp : p (fun j => t j.succ) = ((X.level n).smash (Y.level k)).point :=
          p.property _ ⟨i,hi⟩
        rw [hp,diagonalGridBondLeft_point]

/-- The vertical transition is exactly stabilization in the original
fixed-space smash prespectrum. -/
noncomputable def diagonalGridLoopVertical (X Y : Prespectrum.{0}) (n k r : ℕ) :=
  stabilizeLoop (spaceSmash (X.level n) Y) k r

end KIP126.StableHomotopy.Implementation.Prespectrum
