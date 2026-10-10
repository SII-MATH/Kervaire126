import KIP126.Def.Synthetic.Completion.Proofs
import KIP126.Def.Synthetic.Bockstein.Layer.Zero.Raw.Proofs
import KIP126.Def.Synthetic.Bockstein.Maps.Proofs
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import Lean.Elab.Command

/-! Strict dependency regression for the extracted proofs. Unlike the
unfinished Main applications, every declaration below must be independent
of sorryAx, Challenge2, and historical KIPBase assumptions. -/

open Lean Elab Command

run_cmd do
  let declarations := #[
    ``KIP126.Synthetic.Context.lambdaResidualSequence_step_comp_lambdaPow,
    ``KIP126.Synthetic.Bockstein.layerZeroSquare,
    ``KIP126.Synthetic.Bockstein.beta_naturality,
    ``KIP126.Core.SpectralSequence.Filtration.eq_succ_of_associatedGraded_isZero,
    ``KIP126.Core.SpectralSequence.Filtration.eq_of_associatedGraded_isZero,
    ``KIP126.Synthetic.SpectralSequence.TowerConvergence.associatedGraded_isZero_of_eInfty_isZero,
    ``KIP126.Synthetic.SpectralSequence.TowerConvergence.filtrationAtLeast_iff_of_eInfty_isZero,
    ``KIP126.Synthetic.SpectralSequence.TowerConvergence.eq_zero_of_eInfty_isZero_ge]
  for name in declarations do
    let axioms ← liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Migrated proof {name} has an unexpected axiom dependency: {axiomName}"
  for moduleName in (← getEnv).allImportedModuleNames do
    if (`KIPBase).isPrefixOf moduleName ||
        (`KIP126.Interface).isPrefixOf moduleName ||
        (`KIP126.Main).isPrefixOf moduleName then
      throwError "Migrated foundations import a historical or project input: {moduleName}"
