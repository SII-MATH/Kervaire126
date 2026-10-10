import KIP126.Checks.ClassicalAdams.StandardSquareGeneric
import KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs
import Lean.Elab.Command

/-! The fixed specialization uses the existing foundation and Milnor
coordinates projected from Def's fixed implementation. Its Mathlib sphere-page
objects and proof live in the StandardSphere adapter. The separate
StandardSquareGeneric check preserves the generic proof's independence from
adapters, Lin data and stage witnesses; this check audits the fixed dependency. -/

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let fixed := ``KIP126.Classical.Adams.sphereH6Square_ne_zero
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.standardMilnorCooperations]
  let axioms ← liftCoreM (collectAxioms fixed)
  for a in axioms do
    unless KIP126.Checks.AxiomInputs.allows (logical ++ inputs) a do
      throwError "unexpected fixed standard-square dependency: {a}"
  for m in (← getEnv).allImportedModuleNames do
    let sphereAdapter := [
      `KIP126.Mathlib.ClassicalAdams.StandardSphere.Data,
      `KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs]
    if ((`KIP126.Mathlib).isPrefixOf m && !sphereAdapter.contains m) ||
        (`KIPBase).isPrefixOf m ||
        (`KIP126.LinProgram).isPrefixOf m then
      throwError "unexpected standard-square import: {m}"

#print axioms KIP126.Classical.Adams.sphereH6Square_ne_zero
