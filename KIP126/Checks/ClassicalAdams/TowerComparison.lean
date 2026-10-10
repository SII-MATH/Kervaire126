import KIP126.Checks.AxiomInputs
import KIP126.Mathlib.ClassicalAdams.Comparison.Construction.Data
import KIP126.Mathlib.ClassicalAdams.SurvivalComparison.Proofs
import Lean.Elab.Command

/-! Audit the all-page and survival comparisons separately from the Lin
presentation, Milnor coordinates, and the remaining class comparison assumption. -/
open Lean Elab Command in
run_cmd do
  let foundational := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsTowerPageComparison,
      ``KIP126.Classical.Adams.adamsTowerPageComparison_differential,
      ``KIP126.Classical.Adams.adamsTowerPageComparison_passage,
      ``KIP126.Classical.Adams.adamsTowerSSData_next_relation,
      ``KIP126.Classical.Adams.adamsPageHomologyIso_relation,
      ``KIP126.Core.SpectralSequence.isPermanent_iff_indexed,
      ``KIP126.Classical.Adams.adamsTower_isPermanent_iff_compatible,
      ``KIP126.Classical.Adams.adamsTower_survival_comparison] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless KIP126.Checks.AxiomInputs.allows foundational a do
        throwError "unexpected generic tower comparison dependency: {declaration}: {a}"
  let comparison := ``KIP126.Classical.Adams.sphereAdams_towerComparison
  let some (.defnInfo _) := (← getEnv).find? comparison
    | throwError "the sphere tower comparison must be constructed, not postulated"
  for a in ← liftCoreM (collectAxioms comparison) do
    unless KIP126.Checks.AxiomInputs.allows (``KIP126.Classical.Adams.standardFoundation :: foundational) a do
      throwError "unexpected fixed tower comparison dependency: {a}"
  let survival := ``KIP126.Classical.Adams.survival_comparison
  let some (.thmInfo _) := (← getEnv).find? survival
    | throwError "the survival comparison must be proved, not postulated"
  for a in ← liftCoreM (collectAxioms survival) do
    unless KIP126.Checks.AxiomInputs.allows (``KIP126.Classical.Adams.standardFoundation :: foundational) a do
      throwError "unexpected survival comparison dependency: {a}"

#print axioms KIP126.Classical.Adams.adamsTowerPageComparison_differential
#print axioms KIP126.Classical.Adams.adamsTowerPageComparison_passage
#print axioms KIP126.Classical.Adams.sphereAdams_towerComparison
#print axioms KIP126.Classical.Adams.survival_comparison
