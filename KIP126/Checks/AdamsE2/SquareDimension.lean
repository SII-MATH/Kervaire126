import KIP126.Checks.AxiomInputs
import KIP126.LinProgram.Certificates.SquareDimension.Proofs
import KIP126.Main.Solution.Computation.Dimension
import Lean.Elab.Command

/-! The small degree argument is kernel-checked, not an additive-basis
certification axiom. The internal transfer uses the foundation projection and
Lin comparison on the same implementation fixed in Def. -/

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.LinE2.generatorDegree_eq_row,
      ``KIP126.LinE2.generatorDegree_low_filtration,
      ``KIP126.LinE2.squareDegree_support,
      ``KIP126.LinE2.monomialDegree_square_unique,
      ``KIP126.LinE2.homogeneousPart_square_eq_span,
      ``KIP126.LinE2.E2At_square_eq_zero_or] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected square-dimension dependency: {declaration}: {a}"
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation]
  for declaration in [``KIP126.Classical.Adams.sphereAdamsData_square_eq_zero_or,
      ``KIP126.Classical.Adams.sphereAdamsData_eq_computedH6Square_of_ne_zero] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (logical ++ inputs)
      declaration "unexpected internal square-dimension dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected internal square-dimension import: {m}"

#print axioms KIP126.LinE2.monomialDegree_square_unique
#print axioms KIP126.LinE2.E2At_square_eq_zero_or
#print axioms KIP126.Classical.Adams.sphereAdamsData_eq_computedH6Square_of_ne_zero
