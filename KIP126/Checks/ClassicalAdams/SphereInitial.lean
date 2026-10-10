import KIP126.Def.ClassicalAdams.SphereInitial.Permanence.Proofs
import KIP126.Def.ClassicalAdams.SphereInitial.FiltrationOne.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.PageTwo.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Sphere.Nonvanishing.Proofs
import Lean.Elab.Command

/-! The actual sphere initial column and its internal survival statement
need no ring, Künneth, Milnor, Lin, or fixed-foundation input. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.adamsUnit_sphere_unitor,
      ``KIP126.StableHomotopy.Cohomology.mod2SphereHomology_exists_ne_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageTwo_nonzero_of_first_cycle,
      ``KIP126.StableHomotopy.Cohomology.mod2SphereHomology_unit_surjective,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap_unit_image,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap_sphere,
      ``KIP126.Classical.Adams.sphereAdamsResolutionBoundary_zero,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageD_one_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsK_zero,
      ``KIP126.Classical.Adams.sphereAdamsCycles_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsDifferential_filtration_zero,
      ``KIP126.Classical.Adams.adamsBoundaries_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsCycleSubmodule_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsBoundarySubmodule_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsSSData_Z_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdamsSSData_B_filtration_zero,
      ``KIP126.Classical.Adams.sphereAdams_nonzeroSurvival_filtration_zero_iff,
      ``KIP126.Classical.Adams.adamsBoundaries_succ_eq_of_differential_zero,
      ``KIP126.Classical.Adams.sphereAdamsBoundaries_filtration_one_succ,
      ``KIP126.Classical.Adams.sphereAdamsBoundaries_filtration_one] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected sphere-initial dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth).isPrefixOf m ||
        (`KIP126.Def.Steenrod.MilnorCobar).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected sphere-initial import: {m}"

#print axioms KIP126.Classical.Adams.sphereAdamsSSData_Z_filtration_zero
#print axioms KIP126.Classical.Adams.sphereAdams_nonzeroSurvival_filtration_zero_iff
#print axioms KIP126.Classical.Adams.sphereAdamsBoundaries_filtration_one
