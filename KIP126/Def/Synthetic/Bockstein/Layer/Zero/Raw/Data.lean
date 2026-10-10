import KIP126.Def.Synthetic.Bockstein.Tower.Data

/-! The actual source and target identifications for the zeroth residual
arrow. The target retains the specified zero-shift isomorphism. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Only the actual integer/natural index normalization is used on the source. -/
noncomputable def layerZeroSourceIso (A : Syn) :
    (lambdaTower A).obj 1 ≅ (SyntheticCategory.biShift (0, -1)).obj A :=
  eqToIso (by rfl)

/-- The actual zeroth tower object is identified with A by the existing
zero-shift comparison, rather than by a definitional identification. -/
noncomputable def layerZeroTargetIso (A : Syn) :
    (lambdaTower A).obj 0 ≅ A :=
  SyntheticCategory.biShift_zero.app A

end KIP126.Synthetic.Bockstein
