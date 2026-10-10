import KIP126.Main.Solution.Computation.Tower.Survival
import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.Differential.Second
import Lean.Elab.Command

/-! The actual tower representative is identified without a fixed Milnor
coordinate axiom or a Mathlib spectral-sequence adapter. The additional
below-page structures and coherence conditions remain explicit parameters. -/

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsCycles_mem_iff_of_page_eq,
      ``KIP126.Classical.Adams.sphereAdams_h6_nonzeroSurvival_iff_representative,
      ``KIP126.Classical.Adams.adamsTowerPreSS_d_two_h6_eq,
      ``KIP126.Classical.Adams.adamsTower_d_two_h6_comparison,
      ``KIP126.Classical.Adams.adamsTower_d_two_h6_representative,
      ``KIP126.Classical.Adams.adamsTower_d_two_h6_value_of_lift,
      ``KIP126.Classical.Adams.adamsTower_d_two_h6_value_exists,
      ``KIP126.Classical.Adams.adamsTower_d_two_h6_eq_zero_iff_lift] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected representative-independence dependency: {declaration}: {a}"
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation]
  for declaration in [``KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_computedH6Square,
      ``KIP126.Classical.Adams.computedH6Square_double_representative,
      ``KIP126.Classical.Adams.computedH6Square_of_double_representative,
      ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_double_lifts,
      ``KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_double_connecting_lifts,
      ``KIP126.Classical.Adams.computedH6Square_d_two_value_of_double_lift,
      ``KIP126.Classical.Adams.computedH6Square_d_two_double_value_exists,
      ``KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_iff_double_lift,
      ``KIP126.Classical.Adams.computedH6Square_double_lift_five_of_leibniz] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (logical ++ inputs)
      declaration "unexpected computational tower dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected computational tower import: {m}"

#print axioms KIP126.Classical.Adams.sphereH6DoubleInternalE2_eq_computedH6Square
#print axioms KIP126.Classical.Adams.computedH6Square_double_representative
#print axioms KIP126.Classical.Adams.computedH6Square_nonzeroSurvival_iff_double_connecting_lifts
#print axioms KIP126.Classical.Adams.adamsTower_d_two_h6_eq_zero_iff_lift
#print axioms KIP126.Classical.Adams.computedH6Square_d_two_value_of_double_lift
#print axioms KIP126.Classical.Adams.computedH6Square_d_two_eq_zero_iff_double_lift
#print axioms KIP126.Classical.Adams.computedH6Square_double_lift_five_of_leibniz
