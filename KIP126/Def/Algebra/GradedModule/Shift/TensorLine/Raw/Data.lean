import KIP126.Def.Algebra.GradedModule.Shift.Data
import KIP126.Def.Algebra.GradedModule.Trivial.Data
import KIP126.Def.Algebra.GradedComodule.Shift.TensorLine.Data

/-!
The coefficient-line identification for a left-module shift.  The tensor
factors have degrees `u,t` in that order.  Scalar multiplication gives degree
`u+t`, followed only by the explicit equality with `t+u`.
-/

namespace KIP126.Algebra.GradedModule.TensorLine

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- The canonical underlying isomorphism for right tensoring degree lines.
Its forward map multiplies the scalar coordinates; it is not selected by choice. -/
noncomputable def iso (t u : ℤ) :
    GradedComodule.degreeLine K u ⊗ GradedComodule.degreeLine K t ≅
      GradedComodule.degreeLine K (t + u) :=
  GradedComodule.degreeLineTensorIso K u t ≪≫
    eqToIso (by rw [add_comm u t])

end KIP126.Algebra.GradedModule.TensorLine
