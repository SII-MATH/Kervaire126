import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
import KIP126.Def.ClassicalAdams.TowerSSData.PagePassage.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Image.Proofs
import Lean.Elab.Command

/-! Reject both trust debt and reverse imports in the actual tower construction.
This audits the generic construction independently of the chosen sphere foundation. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsTowerSSData,
      ``KIP126.Classical.Adams.adamsTowerSSDataPageIso,
      ``KIP126.Classical.Adams.adamsNextCycle_exists_of_differential_eq_zero,
      ``KIP126.Classical.Adams.adamsNextCycle_quotient_eq_of_page_eq,
      ``KIP126.Classical.Adams.adamsTowerE2OfFirstCycle,
      ``KIP126.Classical.Adams.adamsTowerE2OfFirstCycle_comparison,
      ``KIP126.Classical.Adams.adamsTowerE2OfFirstCycle_eq_zero_iff,
      ``KIP126.Classical.Adams.adamsNextBoundary_iff_is_differential,
      ``KIP126.Classical.Adams.adamsTowerE2OfFirstCycle_eq_zero_iff_is_differential,
      ``KIP126.Classical.Adams.adamsTowerPreSS,
      ``KIP126.Classical.Adams.adamsTowerInternalSpectralSequence,
      ``KIP126.Classical.Adams.adamsTowerSSDataPageIso_π,
      ``KIP126.Classical.Adams.adamsTowerInternalD_kernel,
      ``KIP126.Classical.Adams.adamsTowerInternalD_image,
      ``KIP126.Classical.Adams.adamsTowerInternalD_comparison,
      ``KIP126.Classical.Adams.adamsTowerInternalD_comp,
      ``KIP126.Classical.Adams.adamsTowerSSData_next_relation,
      ``KIP126.Classical.Adams.adamsNextPage_representative_independence,
      ``KIP126.Classical.Adams.adamsPages_common_representative,
      ``KIP126.Classical.Adams.adamsTowerSSData_top_projection_ne_zero,
      ``KIP126.Classical.Adams.adamsTower_nonzeroSurvival_iff,
      ``KIP126.Classical.Adams.adamsTower_nonzeroSurvival_iff_compatible,
      ``KIP126.Classical.Adams.mem_adamsCycleSubmodule_top,
      ``KIP126.Classical.Adams.mem_adamsBoundarySubmodule_top,
      ``KIP126.Core.SpectralSequence.submoduleCokernelIso_π] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected axiom in tower construction: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected tower-construction import: {m}"

#print axioms KIP126.Classical.Adams.adamsTowerSSDataPageIso
#print axioms KIP126.Classical.Adams.adamsTowerPreSS
#print axioms KIP126.Classical.Adams.adamsTowerInternalSpectralSequence
#print axioms KIP126.Classical.Adams.adamsTower_nonzeroSurvival_iff_compatible
