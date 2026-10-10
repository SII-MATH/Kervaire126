import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Lifting.Proofs
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation]
  for declaration in [``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_boundaryLifts,
      ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_firstCycleProductRule] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (logical ++ inputs)
      declaration "unexpected fixed boundary-lift dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected fixed boundary-lift import: {m}"

#print axioms KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_boundaryLifts
#print axioms KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_firstCycleProductRule
