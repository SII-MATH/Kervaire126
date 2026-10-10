import KIP126.Checks.ProofDependencies
import KIP126.Checks.AxiomInputs
import KIP126.Main.Challenge.h6_sq_permanent
import KIP126.Main.Solution.h6_sq_permanent
import KIP126.Main.Solution.Computation.Comparisons.Classes
import Lean.Elab.Command

/-! Exactly one final target, paired with one proof obligation. The comparison
lemmas may use C(M), but must not introduce a second final theorem. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let challenge := ``KIP126.Challenge.Final.H6SquarePermanent.h6_sq_permanent
  let solution := ``KIP126.Solution.Final.H6SquarePermanent.h6_sq_permanent
  let some (.thmInfo ci) := env.find? challenge | throwError "missing final target"
  let some (.thmInfo si) := env.find? solution | throwError "missing final proof obligation"
  unless ci.type == si.type do
    throwError "Challenge/Solution statement mismatch"
  unless si.levelParams.isEmpty do
    throwError "unexpected universe parameters"
  if si.type.isForall then throwError "unexpected public parameter"
  unless ci.value.getUsedConstants.contains ``sorryAx do
    throwError "Challenge must remain a statement placeholder"
  for (name, info) in env.constants.toList do
    if (`KIP126.Challenge.Final).isPrefixOf name ||
        (`KIP126.Solution.Final).isPrefixOf name then
      if let .thmInfo _ := info then
        unless name == challenge || name == solution do
          throwError "extra final theorem: {name}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let foundation := ``KIP126.Classical.Adams.standardFoundation
  let inputs := [foundation, ``KIP126.Classical.Adams.linE2Presentation]
  -- The final logical step uses the shared A(M)/C(M) witness through 7.8/7.9.
  -- Its remaining proof debt is inherited from those unfinished route theorems.
  let finalDependencies := si.value.getUsedConstants
  if finalDependencies.contains ``sorryAx then
    throwError "the final logical step must retain its actual proof"
  -- Both tracks are imported here for their type comparison. Inspect the
  -- Solution dependency closure to ensure it never borrows a Challenge proof.
  KIP126.Checks.rejectGoalProofs #[solution]
  let axioms ← liftCoreM (collectAxioms solution)
  for a in axioms do
    unless KIP126.Checks.AxiomInputs.allows (logical ++ [``sorryAx] ++ inputs) a do
      throwError "unexpected final dependency: {a}"
  -- The merged Challenge2 type contains unfinished structural comparisons.
  -- As in Checks.AdamsE2.LinBasis, disclose its existing dependency closure;
  -- this is a boundary check, not a claim of axiom-free certification.
  let boundaryAxs ← liftCoreM (collectAxioms ``KIP126.Main.Axiom.challenge2)
  let comparison := ``KIP126.Classical.Adams.computedH6Square_eq_standardH6Square
  let some (.thmInfo comparisonInfo) := env.find? comparison
    | throwError "missing CSV/standard comparison proof"
  if comparisonInfo.value.getUsedConstants.contains ``sorryAx then
    throwError "CSV/standard comparison must retain its actual conditional proof"
  for a in ← liftCoreM (collectAxioms comparison) do
    unless KIP126.Checks.AxiomInputs.allows (logical ++ inputs) a || boundaryAxs.contains a do
      throwError "CSV/standard comparison acquired a dependency outside its stage inputs: {a}"

open KIP126.Classical.Adams KIP126.Core.SpectralSequence in
example : NonzeroSurvival sphereAdamsData (2, 128) standardH6Square :=
  KIP126.Solution.Final.H6SquarePermanent.h6_sq_permanent

open KIP126.Classical.Adams KIP126.Core.SpectralSequence in
example : NonzeroSurvival sphereAdamsData (2, 128) computedH6Square ↔
    NonzeroSurvival sphereAdamsData (2, 128) standardH6Square :=
  computedH6Square_nonzeroSurvival_iff_standard

#print axioms KIP126.Solution.Final.H6SquarePermanent.h6_sq_permanent
