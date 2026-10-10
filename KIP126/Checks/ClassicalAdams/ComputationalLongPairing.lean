import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Proofs
import Lean.Elab.Command

/-! The fixed computational corollary discloses its foundation and Lin
presentation inputs. No undeclared geometric axiom is allowed. In development,
admitted package-type `sorryAx` is reported; strict completion remains explicit. -/
open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let foundation := ``KIP126.Classical.Adams.standardFoundation
  for a in ← liftCoreM (collectAxioms
      ``KIP126.Classical.Adams.LinE2Presentation.h6_cross_products_add_eq_zero) do
    unless KIP126.Checks.AxiomInputs.allows (logical ++ [foundation]) a do
      throwError "unexpected explicit-presentation cancellation dependency: {a}"
  let inputs := [foundation, ``KIP126.Classical.Adams.linE2Presentation]
  for declaration in [``KIP126.Classical.Adams.SphereH6LongLayerMaps.LinCompatible,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.LinCompatible.cross_sum_zero,
      ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_longLayer] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (logical ++ inputs)
      declaration "unexpected computational long-pairing dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected computational long-pairing import: {m}"

#print axioms KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_of_longLayer
