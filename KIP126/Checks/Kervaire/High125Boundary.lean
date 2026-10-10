import KIP126.Main.Solution.Computation.Tmf
import Lean.Elab.Command

/-! Guard the distinction between the prior tmf source and Main's deduction
of nonzero associated grade. Pending proofs are allowed; a stage consumer
axiom or an Interface Application field cannot supply the conclusion. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `KIP126.Literature.Route.Application.tmf then
    throwError "Interface Application must not carry Main's high125 deduction"
  for m in env.allImportedModuleNames do
    if (`KIP126.Interface.Solution).isPrefixOf m ||
        (`KIP126.Main.Axiom).isPrefixOf m then
      throwError "independent high125 deduction imports a producer or consumer stage: {m}"
  for name in [
      ``KIP126.Main.Solution.Computation.high125_nonzero_survival_of_computation,
      ``KIP126.Main.Solution.Computation.tmf_of_source,
      ``KIP126.Main.Solution.Computation.tmf_inputs_of_computation] do
    let some (.thmInfo _) := env.find? name
      | throwError "missing Main high125 proof obligation: {name}"
    let axioms ← liftCoreM (collectAxioms name)
    if axioms.contains `KIP126.Main.Axiom.challenge2 then
      throwError "independent high125 deduction consumes Challenge2: {name}"
  let some info := env.find?
      ``KIP126.Main.Solution.Computation.high125_nonzero_survival_of_computation
    | throwError "missing high125 survival deduction"
  for premise in [``KIP126.Computation.Route.Inputs,
      ``KIP126.Classical.Adams.SphereVanishingLine,
      ``KIP126.Classical.Adams.ClassicalSphereSeparated,
      ``KIP126.Literature.Route.TmfSourceResults,
      ``KIP126.Literature.Route.ClassicalProductDetection] do
    unless info.type.getUsedConstants.contains premise do
      throwError "high125 deduction dropped its explicit prerequisite: {premise}"
