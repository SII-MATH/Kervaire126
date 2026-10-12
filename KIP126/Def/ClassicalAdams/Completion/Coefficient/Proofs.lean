module

public import KIP126.Def.ClassicalAdams.Completion.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [(tensorLeft H.HF2).Additive]

include R in
/-- The coefficient-smash residual tower is acyclic because its actual
transition morphisms vanish by the coefficient multiplication and unit. -/
theorem coefficientAdamsSequence_isAcyclic (X : C) :
    ((adamsResidualSequence H.unit X).map (tensorLeft H.HF2)).IsAcyclic :=
  InverseSequence.isAcyclic_of_step_eq_zero _ (mod2_adamsTowerStep_eq_zero H R X)

include R in
/-- Detection by coefficients and the comparison with this particular
residual product imply Adams nilpotent completeness. These two properties
must still be established for the supplied category and tower. -/
theorem isENilpotentComplete_of_coefficient_product_comparison (X : C)
    [(tensorLeft H.HF2).ReflectsIsomorphisms]
    [IsIso (piComparison (tensorLeft H.HF2) (adamsResidualSequence H.unit X).obj)] :
    IsENilpotentComplete H.unit X :=
  InverseSequence.isAcyclic_of_map_step_eq_zero _ (tensorLeft H.HF2)
    (mod2_adamsTowerStep_eq_zero H R X)

end KIP126.Classical.Adams
