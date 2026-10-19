module

public import KIP126.Main.Solution.StageInput.Bindings
public import KIP126.Main.Solution.StageInput.Toda
public import KIP126.Main.Solution.StageInput.NuSource
public import KIP126.Main.Solution.Computation.Tmf
public import KIP126.Main.Solution.Computation.Tmf.Br21
public import KIP126.Def.StageInput.StandardSphere.Sequence.Proofs
public import KIP126.Def.StageInput.StandardSphere.EInfty.Proofs
public import KIP126.Interface.Solution.Literature.Route.Adapters

@[expose] public section

/-! Assemble the route inputs from separately compiled comparisons and computation results. -/
namespace KIP126.Main.StageInput

theorem sphereSeparated :
    KIP126.Classical.Adams.ClassicalSphereSeparated KIP126.Classical.Adams.standardFoundation.hf2 :=
  KIP126.Def.standardSphereSeparated

/-- Main combines the same source results with Def's naturality of the
fixed synthetic weight comparison. -/
noncomputable def routeStatements :
    KIP126.Literature.Route.Statements routeModel routeEta tmfLabels
      literature.bindings.route :=
  literature.results.route
    KIP126.Def.standardEInftyWeightShift_natural

/-- Main assembles the internal source application on the same bindings.
The secondary Toda comparison and compatible ν triple are derived in the
separate proof modules from the same source bindings. -/
theorem routeApplication :
    KIP126.Literature.Route.Application routeModel routeEta tmfLabels
      literature.bindings.route := by
  exact KIP126.Interface.Solution.Literature.Route.application_of_parts
    routeModel routeEta tmfLabels literature.bindings.route routeStatements
    completionApplicability completionComparison realizationComparison
    todaSecondaryComparison nuSourceResults

/-- Main derives the tmf consumer facts from the same source, C(M) and tail
premises. In particular high125 survival is not a Challenge2 field. -/
theorem routeTmf :
    KIP126.Literature.Route.TmfInputs routeModel tmfLabels :=
  KIP126.Main.Solution.Computation.tmf_inputs_of_computation routeModel
    routeComputation sphereVanishing sphereSeparated
    literature.bindings.route.tmfSource routeStatements.tmf
    literature.bindings.route.tmfBinding
    literature.bindings.route.algebraBinding.classical_detection

/-- The applied consumer API combines prior sources and comparisons with
Main's tmf deduction on the same shared model. -/
noncomputable def routeLiterature :
    KIP126.Literature.Route.Inputs routeModel routeEta tmfLabels :=
  KIP126.Literature.Route.Statements.toInputs routeModel routeEta tmfLabels
    routeStatements routeApplication routeTmf

end KIP126.Main.StageInput
