import KIP126.Def.Synthetic.Bockstein.Layer.Zero.Raw.Data
import KIP126.Def.Synthetic.Completion.Proofs

/-! The zeroth residual arrow and the specified first lambda power form
an isomorphism square. This uses the actual recursive power, with no
additional identification of that power with lam. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

set_option backward.isDefEq.respectTransparency false in
/-- The n=0 residual-step/power compatibility, with the actual source
normalization and the same biShift_zero target comparison. -/
theorem layerZeroSquare (A : Syn) :
    (layerZeroSourceIso A).hom ≫ lambdaPow 1 A =
      (lambdaTower A).step 0 ≫ (layerZeroTargetIso A).hom := by
  dsimp only [layerZeroSourceIso, layerZeroTargetIso, lambdaTower,
    InverseSequence.toDescendingTower, lambdaResidualSequence]
  simp [lambdaPow]

end KIP126.Synthetic.Bockstein
