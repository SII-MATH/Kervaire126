import KIP126.Checks.ProofDependencies
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differentials.Certificate
import KIP126.Main.Solution.Computation.Tower.Survival
import KIP126.Main.Solution.Computation.LinProgram.Basis.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Basis.Proofs
import KIP126.Main.Solution.Computation.Comparisons.Classes
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Cancellation.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Lifting.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differentials.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Expressions.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Presentation.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Selected.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Tower.Proofs
import KIP126.Main.Solution.Computation.Differential.Second
import KIP126.Main.Solution.Computation.LinProgram.Route.Records
import KIP126.Main.Solution.Literature.EtaRows.Proofs
import KIP126.Main.Solution.Literature.HopfCofiber.Proofs
import KIP126.Main.Solution.Literature.Near126.Sphere.Boundaries.Proofs
import KIP126.Main.Solution.Literature.Near126.Sphere.Conditions.Proofs
import KIP126.Main.Solution.Literature.Near126.Sphere.Proofs
import KIP126.Main.Solution.Literature.Route.Applicability
import KIP126.Main.Solution.Literature.Route.Inputs
import KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs
import Lean.Elab.Command

/-! The Main input consequences remain theorem declarations available via Solution.
Their checked types come from those declarations, without an intermediate
Challenge mirror. No imported proof may depend on a Challenge module. This is
a declaration/dependency check, not a proof-completion audit. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main.Challenge).isPrefixOf m ||
        (`KIP126.Def.Challenge).isPrefixOf m then
      throwError "Solution imports a Challenge placeholder module: {m}"
  let solutions : List Name := [
    ``KIP126.Computation.LinProofs.sphereTable_sound,
    ``KIP126.LinE2.dataBasis_val,
    ``KIP126.LinE2.basisTable_correct,
    ``KIP126.LinE2.dataBasis_ne_zero,
    ``KIP126.LinE2.dataCoordinates_basis,
    ``KIP126.LinE2.dataCoordinates_reconstruct,
    ``KIP126.LinE2.data_finrank,
    ``KIP126.Classical.Adams.sphereE2Coordinates_basis,
    ``KIP126.Classical.Adams.linToSphereE2_dataBasis,
    ``KIP126.Classical.Adams.sphereE2Basis_ne_zero,
    ``KIP126.Classical.Adams.sphereE2Coordinates_reconstruct,
    ``KIP126.Classical.Adams.computedH6Square_eq_standardH6Square,
    ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_standard,
    ``KIP126.Classical.Adams.computedH6_mul_self,
    ``KIP126.Classical.Adams.LinE2Presentation.h6_cross_products_add_eq_zero,
    ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_boundaryLifts,
    ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_firstCycleProductRule,
    ``KIP126.Classical.Adams.SphereH6LongLayerMaps.LinCompatible.cross_sum_zero,
    ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_longLayer,
    ``KIP126.Classical.Adams.sphereE2SecondDifferential_h6_square,
    ``KIP126.Classical.Adams.LinE2Presentation.secondDifferential_eq_zero_iff,
    ``KIP126.Classical.Adams.linE2_add_self_eq_zero,
    ``KIP126.Classical.Adams.LinE2Presentation.secondDifferential_square_eq_zero,
    ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_leibniz,
    ``KIP126.Computation.LinProofs.differential_of_lookup,
    ``KIP126.Computation.LinProofs.DifferentialStatement.hasDifferential,
    ``KIP126.Computation.LinProofs.row5541,
    ``KIP126.Classical.Adams.expressionOnSphere_zero,
    ``KIP126.Classical.Adams.expressionOnSphere_add,
    ``KIP126.Classical.Adams.expressionOnSphere_mul,
    ``KIP126.Classical.Adams.expressionOnSphere_h6,
    ``KIP126.Classical.Adams.expressionOnSphere_h6_square,
    ``KIP126.Classical.Adams.linToSphere_exists_preimage,
    ``KIP126.Classical.Adams.linToSphere_eq_iff,
    ``KIP126.Classical.Adams.linToSphere_ne_zero_iff,
    ``KIP126.Classical.Adams.linToSphere_mul,
    ``KIP126.Classical.Adams.linToSphere_product_eq,
    ``KIP126.Classical.Adams.linToSphere_product_eq_zero,
    ``KIP126.Computation.LinProofs.Selected.d2_x_125_8,
    ``KIP126.Computation.LinProofs.Selected.d2_h6,
    ``KIP126.Computation.LinProofs.Selected.d3_h4_x_109_12,
    ``KIP126.Computation.LinProofs.Selected.d3_h0Sq_x_123_13_2,
    ``KIP126.Computation.LinProofs.Selected.d3_x_126_4,
    ``KIP126.Computation.LinProofs.Selected.d7_x_123_11_combination,
    ``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_computedH6Square,
    ``KIP126.Classical.Adams.computedH6Square_double_representative,
    ``KIP126.Classical.Adams.computedH6Square_of_double_representative,
    ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_double_lifts,
    ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_double_connecting_lifts,
    ``KIP126.Classical.Adams.computedH6Square_d_two_value_of_double_lift,
    ``KIP126.Classical.Adams.computedH6Square_d_two_double_value_exists,
    ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_iff_double_lift,
    ``KIP126.Classical.Adams.computedH6Square_double_lift_five_of_leibniz,
    ``KIP126.Computation.Route.Inputs.d3_cnu_bottom_x_126_8,
    ``KIP126.Computation.Route.Inputs.d3_cnu_bottom_x_126_8_2,
    ``KIP126.Computation.Route.Inputs.X_reaches_e6,
    ``KIP126.Computation.Route.Inputs.W_reaches_e6,
    ``KIP126.Computation.Route.Inputs.V_reaches_e12,
    ``KIP126.Computation.Route.Inputs.Y_reaches_e5,
    ``KIP126.Computation.Route.Inputs.T_reaches_e1000,
    ``KIP126.Computation.Route.Inputs.d2_h6,
    ``KIP126.Computation.Route.Inputs.d2_x_125_8,
    ``KIP126.Computation.Route.Inputs.d3_h4_x_109_12,
    ``KIP126.Computation.Route.Inputs.d3_h0Sq_x_123_13_2,
    ``KIP126.Computation.Route.Inputs.d3_x_126_4,
    ``KIP126.Computation.Route.Inputs.d7_x_123_combination,
    ``KIP126.Computation.Route.Inputs.d3_cnu_top,
    ``KIP126.Computation.Route.Inputs.refutation_2047477,
    ``KIP126.Computation.Route.Inputs.refutation_2047478,
    ``KIP126.Computation.Route.Inputs.refutation_154532,
    ``KIP126.Computation.Route.Inputs.refutation_154533,
    ``KIP126.Computation.Route.Inputs.refutation_154534,
    ``KIP126.Computation.Route.Inputs.refutation_154535,
    ``KIP126.Computation.Route.Inputs.refutation_154536,
    ``KIP126.Computation.Route.Inputs.refutation_154537,
    ``KIP126.Computation.Route.Inputs.d2_h0Six_h6,
    ``KIP126.Computation.Route.Inputs.d2_for_P_h2,
    ``KIP126.Computation.Route.Inputs.d2_for_Q_h2_first,
    ``KIP126.Computation.Route.Inputs.d2_for_Q_h2_second,
    ``KIP126.Classical.ExtensionSS.EtaRowId.all_length,
    ``KIP126.Classical.ExtensionSS.EtaRowId.mem_all,
    ``KIP126.Classical.ExtensionSS.EtaRowId.row_mem_etaESSDifferentials,
    ``KIP126.Classical.ExtensionSS.EtaRowId.range_row,
    ``KIP126.Classical.ExtensionSS.EtaData.sourceClass_degree,
    ``KIP126.Classical.ExtensionSS.EtaData.targetClass_degree,
    ``KIP126.Classical.ExtensionSS.EtaData.evidence_claim,
    ``KIP126.Classical.Adams.sphereMapCofiber_first_zero,
    ``KIP126.Classical.Adams.sphereMapCofiber_cells_zero,
    ``KIP126.Classical.Adams.sphereMapCofiberInclusionTower_step,
    ``KIP126.Computation.Near126.SphereBoundaryFacts.p_h2_is_d2_cycle,
    ``KIP126.Computation.Near126.SphereBoundaryFacts.q_h2_is_d2_cycle,
    ``KIP126.Computation.Near126.Sphere.d12_iff_differential,
    ``KIP126.Computation.Near126.SphereSurvivalFacts.c3_iff_not_d6,
    ``KIP126.Computation.Near126.SphereSurvivalFacts.hit_t_iff_d12,
    ``KIP126.Computation.Near126.SphereDifferentialFacts.d3_x_126_6_ne_zero,
    ``KIP126.Computation.Near126.SphereSurvivalFacts.y_not_hit_on_page,
    ``KIP126.Literature.Route.NuCofiberApplicability.exponent_sum,
    ``KIP126.Literature.Route.Inputs.differentialLift,
    ``KIP126.Literature.Route.Inputs.nuTriangle,
    ``KIP126.Classical.Adams.sphereH6Square_ne_zero]
  KIP126.Checks.rejectGoalProofs solutions.toArray
  for solution in solutions do
    let some (.thmInfo _) := env.find? solution
      | throwError "missing Solution theorem: {solution}"
    let some moduleIdx := env.getModuleIdxFor? solution
      | throwError "missing Solution module: {solution}"
    let owner := env.header.moduleNames[moduleIdx]!
    -- This compatibility entry re-exports the theorem about Mathlib's sphere
    -- page; its proof correctly belongs to the optional Mathlib adapter.
    if solution == ``KIP126.Classical.Adams.sphereH6Square_ne_zero then
      unless owner == `KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs do
        throwError "Mathlib sphere theorem changed its owner: {solution}: {owner}"
    else
      unless (`KIP126.Main.Solution).isPrefixOf owner do
        throwError "Main theorem moved outside Solution: {solution}: {owner}"
