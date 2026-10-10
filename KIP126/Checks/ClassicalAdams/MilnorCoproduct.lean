import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Primitive.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Reduced.Map.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Cochains.Proofs
import Lean.Elab.Command

/-! The coproduct formula is an explicit below-page condition, not a fixed
existence axiom. Its extension from the reduced basis and unit is proved. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.cooperation_linearMap_ext,
      ``KIP126.StableHomotopy.Cohomology.milnorMonomialPolynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial,
      ``KIP126.StableHomotopy.Cohomology.Mod2MilnorCoproductCompatible,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_reduced_basis,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_lof_tmul,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorCoproduct_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorCoproduct,
      ``KIP126.StableHomotopy.Cohomology.mod2MilnorCoproductCompatible_iff,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorBasis,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorBasis,
      ``KIP126.StableHomotopy.Cohomology.milnorPairExponents_injective,
      ``KIP126.StableHomotopy.Cohomology.cup_milnorMonomialPolynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_basis,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_injective,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorBasis_apply,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_basis,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_injective,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_eq_iff,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorRightUnit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_leftUnit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_rightUnit,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_h6_existsUnique,
      ``KIP126.StableHomotopy.Cohomology.cooperation_ne_zero_of_h6Polynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_primitive_iff,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_polynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorBasis_reduced,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_coeff,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorBasis_support_reduced,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_mem_span_reduced_of_normalized,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorBasis_positive,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorPolynomial_reduced_normalized,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationSquare,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationSquareInclusion,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationSquareInclusion_lof_tmul,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationSquareInclusion_injective,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_reduced_span_le_range,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_existsUnique_reduced_of_normalized,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_reduced_normalized,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_mem_span_reduced,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_mem_span_reduced_of_ne,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_existsUnique_reduced,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_existsUnique_reduced_of_ne,
      ``KIP126.StableHomotopy.Cohomology.cooperationReducedCobarDiagonal,
      ``KIP126.StableHomotopy.Cohomology.cooperationReducedCobarDiagonal_inclusion,
      ``KIP126.StableHomotopy.Cohomology.cooperationReducedCobarDiagonal_polynomial,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationCochainEquiv,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationCochainEquiv_val,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperation_polynomial_boundary_iff,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_primitive_of_h6Polynomial,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_h6_existsUnique] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Milnor-coproduct dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerPages).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerDifferential).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerHomology).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerResolution).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected below-page Milnor-coproduct import: {m}"

#print axioms KIP126.StableHomotopy.Cohomology.cooperation_linearMap_ext
#print axioms KIP126.StableHomotopy.Cohomology.cooperationMilnorCoproduct
#print axioms KIP126.StableHomotopy.Cohomology.mod2MilnorCoproductCompatible_iff
#print axioms KIP126.StableHomotopy.Cohomology.cooperationTensorMilnorPolynomial_injective
#print axioms KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_h6_existsUnique
#print axioms KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_polynomial
#print axioms KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal_existsUnique_reduced_of_ne
#print axioms KIP126.StableHomotopy.Cohomology.cooperationReducedCobarDiagonal_polynomial
#print axioms KIP126.StableHomotopy.Cohomology.reducedCooperation_polynomial_boundary_iff
