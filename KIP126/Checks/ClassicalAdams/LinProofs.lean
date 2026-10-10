import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Differentials
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let expected := logical ++ [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation,
    ``KIP126.Computation.LinProofs.sphereTable_sound]
  for decl in [``KIP126.Computation.LinProofs.differential_of_lookup,
      ``KIP126.Computation.LinProofs.row5541] do
    let axioms ← KIP126.Checks.AxiomInputs.checkStageConsumer expected decl
      "unexpected Lin proofs dependency"
    unless KIP126.Checks.AxiomInputs.uses axioms
        ``KIP126.Computation.LinProofs.sphereTable_sound do
      throwError "missing explicit Challenge 2 database trust boundary: {decl}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Main.Challenge).isPrefixOf m then
      throwError "unexpected Lin proofs import: {m}"

set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 86 0 = none := by rfl
set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 0 128 = none := by rfl

#print axioms KIP126.Computation.LinProofs.row5541
