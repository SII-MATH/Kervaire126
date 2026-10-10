import KIP126.Checks.AxiomInputs
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Proofs
import KIP126.Main.Solution.Computation.Reduction
import KIP126.LinProgram.Certificates.SquareDetection.Certificate
import Lean.Elab.Command

/-! Kernel-proved algebraic soundness, the full finite certificate, and the
fixed E₂ nonvanishing/reduction interfaces. No native evaluation axiom is allowed.
The additional executable diagnostic is not used as a proof. Fixed-model
consumers report admitted package-type debt during development; their strict
completion audit is enabled by `kip126.checks.strictStageConsumerAudit`. -/

open Lean Elab Command in
run_cmd do
  let basic := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.LinE2.SquareDetection.u_cube,
      ``KIP126.LinE2.SquareDetection.u_square_ne_zero,
      ``KIP126.LinE2.SquareDetection.evaluate_polynomialOfPowers,
      ``KIP126.LinE2.SquareDetection.relationCheck_sound,
      ``KIP126.LinE2.SquareDetection.evaluate_truncated_monomial,
      ``KIP126.LinE2.SquareDetection.definingIdeal_le_ker,
      ``KIP126.LinE2.SquareDetection.dataH6Sq_ne_zero_of_check,
      ``KIP126.LinE2.SquareDetection.splitOn_singleton_eq_list,
      ``KIP126.LinE2.SquareDetection.toNat?_eq_chars,
      ``KIP126.LinE2.SquareDetection.monomialOrder_eq_chars,
      ``KIP126.LinE2.SquareDetection.relationCheck_eq_chars,
      ``KIP126.LinE2.SquareDetection.chunkCheck_eq_chars,
      ``KIP126.LinE2.SquareDetection.charsChunkCheck_append,
      ``KIP126.LinE2.SquareDetection.charsChunkCheck_ofList,
      ``KIP126.LinE2.SquareDetection.charsChunkCheck_join,
      ``KIP126.LinE2.SquareDetection.firstRelations_check,
      ``KIP126.LinE2.SquareDetection.allRelationsCheck_of_chunks,
      ``KIP126.LinE2.SquareDetection.archivedChunks_check,
      ``KIP126.LinE2.SquareDetection.allRelationsCheck_eq_true,
      ``KIP126.LinE2.SquareDetection.dataH6Sq_ne_zero] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless KIP126.Checks.AxiomInputs.allows basic a do
        throwError "unexpected detector dependency: {declaration}: {a}"
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation]
  for declaration in [``KIP126.Classical.Adams.computedH6Square_ne_zero_of_check,
      ``KIP126.Classical.Adams.computedH6Square_ne_zero,
      ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (basic ++ inputs)
      declaration "unexpected transferred nonvanishing dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected detector import: {m}"

#print axioms KIP126.LinE2.SquareDetection.dataH6Sq_ne_zero_of_check
#print axioms KIP126.Classical.Adams.computedH6Square_ne_zero_of_check
#print axioms KIP126.LinE2.SquareDetection.allRelationsCheck_eq_true
#print axioms KIP126.Classical.Adams.computedH6Square_ne_zero
#print axioms KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff

/- The checker must reject a relation killing the square itself. Its success
on the archive is not a vacuous constant-true check. -/
example : KIP126.LinE2.SquareDetection.relationCheck "69,2" = false := by
  rw [KIP126.LinE2.SquareDetection.relationCheck_eq_chars]
  decide +kernel

example : KIP126.LinE2.SquareDetection.relationCheck "69,3" = true := by
  rw [KIP126.LinE2.SquareDetection.relationCheck_eq_chars]
  decide +kernel

/- Runtime regression only: success is not exported as a mathematical theorem. -/
#eval do
  if KIP126.LinE2.SquareDetection.allRelationsCheck then
    IO.println "All archived relations pass square detection (additional runtime regression)."
  else
    throw (IO.userError "An archived relation fails square detection.")
