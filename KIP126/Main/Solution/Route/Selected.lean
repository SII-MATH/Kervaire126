module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.Solution.StageInput
public import KIP126.Main.Solution.Computation.Lambda
public import KIP126.Main.Solution.DifferentialReduction.Conclusion
public import KIP126.Main.Solution.Route.Predicates
public import KIP126.Main.Solution.Route.AlphaOne
public import KIP126.Main.Solution.Route.Section7
import all KIP126.Main.Solution.Route.Selected.Assembly

@[expose] public section

namespace KIP126.Main.Solution.Route

open private differential_dichotomy_from_inputs from KIP126.Main.Solution.Route.Selected.Assembly
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Classical.Adams KIP126.Kervaire.Route
open KIP126.Synthetic.Context
open KIP126.Main.StageInput

/-- The existing Cnu calculation instantiated at the fixed C(M). -/
theorem cnu_d3 :
    KIP126.Computation.Route.Derived.CnuDifferential routeComputation.realization := by
  exact KIP126.Computation.Route.cnu_d3 routeComputation

/-- One-step λ injectivity with A and C from the SAME stage witness. -/
theorem lambda_injective_125_130 :
    LambdaInjectiveAt 125 130 (S_0_0 : KIP126.Def.standardRouteInput.Syn) := by
  exact KIP126.Computation.Route.lambda_injective_125_130 routeLiterature routeComputation

/-- The derived Section 7 finite/infinite facts use the delivered vanishing
line on this same model, rather than an unowned tail assumption. -/
theorem sphere_facts :
    KIP126.Computation.Route.Derived.SphereFacts routeComputation.realization := by
  exact KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing

/-- The precise F15 detector injectivity used at all three occurrences
of the tmf argument in Proposition 7.8. -/
theorem detector_injective : DetectorInjectiveAt routeModel 125 130 15 := by
  exact KIP126.Computation.Route.detector_injective_125_130_filtration15
    routeLiterature routeComputation sphereVanishing sphereSeparated

/-- The Section 7 contradiction now consumes the selected Cnu target and
its incoming-page exclusion through the explicit same-witness chain. -/
theorem eta_extension_excluded_of_d6_vanishes :
    KIP126.Solution.Near126.EtaExtensionObstruction.eta_extension_excluded_of_d6_vanishes
      standardMilnorCooperations routeModel routeLabels routeEta := by
  intro _
  exact Section7.eta_extension_excluded_of_d6_vanishes

/-- Proposition 7.8 from this complete delivered input. The body must use
its A/C fields and prove the finite-page/tail/filtration steps in Main. -/
theorem h6_square_differential_dichotomy_and_criterion (input : KIP126.Challenge2) :
    KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence
      standardMilnorCooperations standardRouteModel input.computation.bindings.routeLabels
      KIP126.Def.standardRouteEta := by
  let lit := input.literature
  let B := lit.bindings.route
  let st := lit.results.route
    (KIP126.Main.Solution.Literature.route_moss lit)
    (KIP126.Main.Solution.Literature.eInfty_shift_natural lit)
  let BHS : KIP126.Literature.Route.SyntheticInputs standardRouteModel := st.synthetic.toInputs _ B.bhsCompletion
    B.completionApplicability B.completionComparison
    (KIP126.Interface.Solution.Literature.Route.realizationKernel_of_source _
      B.kernelSource st.realizationKernel B.kernelBinding)
  let RL : KIP126.Literature.Route.RealizationInput standardRouteModel := ⟨B.realization,
    KIP126.Interface.Solution.Literature.Route.realization_detection_of_completed_sources _
      B.realization B.bhsCompletion st.realization B.completionApplicability
      B.completionComparison B.realizationComparison⟩
  let CL := KIP126.Literature.Route.classicalInputsOfSource standardRouteModel KIP126.Def.standardRouteEta
    B.classicalSource st.classical B.classicalBinding B.synthetic_eta
  let TM := KIP126.Main.Solution.Computation.tmf_inputs_of_computation standardRouteModel
    input.computation.route lit.results.sphereVanishing KIP126.Def.standardSphereSeparated
    B.tmfSource st.tmf B.tmfBinding B.algebraBinding.classical_detection
  exact differential_dichotomy_from_inputs BHS RL CL B.algebraBinding.action_filtration TM st.bx input.computation.route
    lit.results.sphereVanishing KIP126.Def.standardSphereSeparated

end KIP126.Main.Solution.Route
