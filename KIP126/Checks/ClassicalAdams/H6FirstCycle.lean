import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Internal.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Coordinates.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Cooperation.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Reduced.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Reduced.Comparison.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Polynomial.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Nonvanishing.Proofs
import Lean.Elab.Command

/-! The polynomial primitive calculation reaches the actual tower d₁
without the fixed MilnorCooperations page-comparison axiom. The low-level
coherence inputs remain explicit parameters. This is not permanence. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.sphereAdamsPageD_one_h6_tensorBoundary,
      ``KIP126.Classical.Adams.sphereAdamsPageD_one_h6_tensorBoundary_existsUnique,
      ``KIP126.Classical.Adams.sphereAdamsPageOne_h6_tensorBoundary_ne_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageOne_h6_nonzero_cycle_exists,
      ``KIP126.Classical.Adams.sphereAdamsPageTwo_h6_nonzero_exists,
      ``KIP126.Classical.Adams.sphereAdamsInternalE2_h6_nonzero_exists,
      ``KIP126.Classical.Adams.sphereH6TensorRepresentative,
      ``KIP126.Classical.Adams.sphereH6DoubleTensorRepresentative,
      ``KIP126.Classical.Adams.sphereH6DoubleTensorRepresentative_ne_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageOne_h6_double_ne_zero,
      ``KIP126.Classical.Adams.sphereH6DoubleTensorRepresentative_d1_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageD_one_h6_double_zero,
      ``KIP126.Classical.Adams.sphereAdamsDifferential_one_h6_double_zero,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_representative,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_polynomial_representative,
      ``KIP126.Classical.Adams.sphereH6DoubleTensorRepresentative_normalized,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_is_differential,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_cobar,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_cooperation_cobar,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_firstBoundary_reduced,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_reduced_comparison,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_reduced_polynomial,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_mem_range_iff_polynomial,
      ``KIP126.Classical.Adams.sphereSecondReducedBoundaryEquiv_h6_double,
      ``KIP126.Classical.Adams.sphereSecondReducedBoundaryEquiv_h6_double_polynomial,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_homologyD1,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_polynomial,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_cobar_boundary,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_ne_zero_iff_cobar_nonboundary,
      ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_ne_zero,
      ``KIP126.Classical.Adams.sphereAdamsInternalE2_h6_double_nonzero_exists] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected h6 first-cycle dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m ||
        (`KIP126.LinProgram).isPrefixOf m then
      throwError "unexpected fixed-input h6 first-cycle import: {m}"

#print axioms KIP126.Classical.Adams.sphereAdamsPageD_one_h6_tensorBoundary
#print axioms KIP126.Classical.Adams.sphereAdamsPageD_one_h6_tensorBoundary_existsUnique
#print axioms KIP126.Classical.Adams.sphereAdamsPageTwo_h6_nonzero_exists
#print axioms KIP126.Classical.Adams.sphereAdamsInternalE2_h6_nonzero_exists
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_representative
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_polynomial_representative
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_cobar
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_zero_iff_cooperation_cobar
#print axioms KIP126.Classical.Adams.sphereAdamsHomologyD1_firstBoundary_reduced
#print axioms KIP126.Classical.Adams.sphereAdamsHomologyD1_mem_range_iff_polynomial
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_ne_zero_iff_cobar_nonboundary
#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_ne_zero
