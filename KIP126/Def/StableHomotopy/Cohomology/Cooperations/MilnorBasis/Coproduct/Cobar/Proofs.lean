import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Primitive.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Cobar.Data
import Mathlib.Algebra.CharP.Two

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)

/-- Under the explicit below-page coproduct comparison, the corrected
actual diagonal is exactly the existing length-one polynomial differential. -/
theorem cooperationCobarDiagonal_polynomial
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorMilnorPolynomial H R B n (cooperationCobarDiagonal H R K n a) =
      differentialPolynomial 1 (cooperationMilnorPolynomial H R B n a) := by
  simp only [cooperationCobarDiagonal, LinearMap.sub_apply, LinearMap.add_apply,
    map_sub, map_add]
  rw [cooperationTensorMilnorPolynomial_leftUnit, cooperationTensorMilnorPolynomial_rightUnit,
    cooperationMilnorCoproduct H R B K hU hM, CharTwo.sub_eq_add]
  simp [differentialPolynomial]

end
end KIP126.StableHomotopy.Cohomology
