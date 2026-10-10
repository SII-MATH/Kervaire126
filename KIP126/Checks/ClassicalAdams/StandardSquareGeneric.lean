import KIP126.Checks.AxiomInputs
import KIP126.Def.ClassicalAdams.SphereClasses.Proofs
import Lean.Elab.Command

/-! The generic standard-square proof must remain independent of Lin data
and stage witnesses. Check its own import closure before the fixed
specialization imports Def's fixed implementation. -/

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.Sphere.classOfMilnorCocycle_eq_zero_iff,
      ``KIP126.Classical.Adams.Sphere.h6Square_ne_zero] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected generic standard-square dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m || (`KIP126.LinProgram).isPrefixOf m ||
        (`KIP126.Interface).isPrefixOf m || (`KIP126.Main).isPrefixOf m then
      throwError "unexpected generic standard-square import: {m}"

#print axioms KIP126.Classical.Adams.Sphere.classOfMilnorCocycle_eq_zero_iff
#print axioms KIP126.Classical.Adams.Sphere.h6Square_ne_zero
