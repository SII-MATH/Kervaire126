import KIP126.Checks.ProofDependencies
import KIP126.Interface.Solution.Literature.Route.Adapters
import KIP126.Interface.Solution.LinProgram.Route.Certification
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.FirstQuotient.Proofs
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationWeights.Proofs
import KIP126.Def.ClassicalAdams.Detection.Convergence.Uniqueness
import KIP126.Def.ClassicalAdams.Detection.Convergence.Proofs
import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
import KIP126.Def.Synthetic.Detection.Proofs
import Lean.Elab.Command

/-! Internal Interface results have a single statement/proof declaration in
Solution. Check availability, proof boundaries and the existing direct proofs;
these checks do not certify unfinished source results or the aggregate producer. -/
noncomputable section
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main.Challenge).isPrefixOf m ||
        (`KIP126.Def.Challenge).isPrefixOf m then
      throwError "Interface Solution imports a Challenge placeholder module: {m}"
  let solutions : List Name := [
      ``KIP126.Interface.Solution.Literature.Route.may_signed_boundary_of_source,
      ``KIP126.Interface.Solution.Literature.Route.may_boundary_projected_of_exponent_two,
      ``KIP126.Interface.Solution.Literature.Route.todaApplication_of_secondary,
      ``KIP126.Interface.Solution.Literature.Route.toda_of_source,
      ``KIP126.Interface.Solution.Literature.Route.realizationKernel_of_source,
      ``KIP126.Interface.Solution.Literature.Route.mossInputOfClassicalSource,
      ``KIP126.Interface.Solution.Literature.Route.nuCofiber_of_source,
      ``KIP126.Interface.Solution.Literature.Route.application_of_parts,
      ``KIP126.Interface.Solution.LinProgram.Route.certify_of_parts,
      ``KIP126.Interface.Solution.LinProgram.Route.certification]
  KIP126.Checks.rejectGoalProofs solutions.toArray
  for solution in solutions do
    let some (.thmInfo si) := env.find? solution
      | throwError "missing Interface Solution theorem: {solution}"
    let some moduleIdx := env.getModuleIdxFor? solution
      | throwError "missing Interface Solution module: {solution}"
    let owner := env.header.moduleNames[moduleIdx]!
    unless (`KIP126.Interface.Solution).isPrefixOf owner do
      throwError "Interface theorem changed its owner: {solution}: {owner}"
    -- These direct proofs must not regress to placeholders; their source or
    -- aggregate inputs may still carry unfinished proof obligations.
    if si.value.getUsedConstants.contains ``sorryAx then
      throwError "Interface helper lost its existing proof: {solution}"
    let axioms ← liftCoreM (collectAxioms solution)
    if axioms.contains `KIP126.Main.Axiom.challenge2 then
      throwError "Interface producer depends on its consumer axiom: {solution}"

open KIP126 KIP126.Classical.Adams KIP126.Computation.Route in
example (I : KIP126.Challenge2) :
    I.computation.results.route.toInputs = I.computation.route := rfl

open KIP126 KIP126.Classical.Adams in
example (I : KIP126.Challenge2)
    (localMoss : Literature.Route.MossSourceInput standardMilnorCooperations
      I.literature.bindings.route.classicalSource.convergence)
    (shiftNatural : I.literature.bindings.eInftyWeightShift.Natural)
    (application : Literature.Route.Application standardRouteModel Def.standardRouteEta
      I.literature.bindings.tmfLabels I.literature.bindings.route)
    (tmf : Literature.Route.TmfInputs standardRouteModel I.literature.bindings.tmfLabels) :
    Literature.Route.Inputs standardRouteModel Def.standardRouteEta I.literature.bindings.tmfLabels :=
  Literature.Route.Statements.toInputs standardRouteModel Def.standardRouteEta
    I.literature.bindings.tmfLabels
    (I.literature.results.route localMoss shiftNatural) application tmf
