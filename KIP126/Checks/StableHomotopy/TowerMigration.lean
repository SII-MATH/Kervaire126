import KIP126.Def.Synthetic.Bockstein.Regrading.Sequence.Data
import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Proofs
import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
import KIP126.Def.Synthetic.Bockstein.Regrading.Proofs
import KIP126.Def.StableHomotopy.InverseSequence.Proofs
import KIP126.Def.StableHomotopy.DescendingTower.Layer.Proofs
import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Proofs
import KIP126.Def.StableHomotopy.TowerSpectralSequence.FirstPage.Proofs
import Lean.Elab.Command

/-!
Dependency regression for the tower-page proof migration. Check every completed
obligation and the existing data constructions consuming these proofs. This
checks transitive axiom dependencies, not merely the absence of local `sorry`.
This also checks the completed PreSS laws, synthetic regrading, actual
weight-shift quotient, and their supporting proofs; no historical model is imported.
-/

open Lean Elab Command

#print axioms KIP126.StableHomotopy.DescendingTower.map_self
#print axioms KIP126.StableHomotopy.DescendingTower.map_succ
#print axioms KIP126.StableHomotopy.DescendingTower.map_adjacent
#print axioms KIP126.StableHomotopy.DescendingTower.map_comp
#print axioms KIP126.StableHomotopy.InverseSequence.toDescendingTower_map_nonpos
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.J_mem_cycles
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.cycles_one
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundaries_one
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.cycles_antitone
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundaries_monotone
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundaries_le_cycles
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.cycleSubmodule_antitone
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundarySubmodule_monotone
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundarySubmodule_le_cycle
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.JToPage_eq
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_of_lift
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_zero_of_K
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_add
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_smul
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.boundaries_le_differential_ker
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differential_JToPage
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differential_comp
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.firstPageProjection_eq_inv
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.firstPageIso_projection
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.ssData
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.pageIso
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.firstPageIso
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differential

#print axioms KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
#print axioms KIP126.Synthetic.SpectralSequence.exists_weightLiftRepresentative
#print axioms KIP126.Classical.Adams.TowerDetection.exists_liftRepresentative
#print axioms KIP126.Synthetic.Bockstein.normalizedPreSS_d_comp_d
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.preSS_d_comp_d
#print axioms KIP126.StableHomotopy.SequentialHomotopyLimit.π_step
#print axioms KIP126.StableHomotopy.SequentialHomotopyLimit.isZero_iff
#print axioms KIP126.StableHomotopy.InverseSequence.toDescendingTower_layer_isZero
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.preSS_Z_succ
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.preSS_B_succ
#print axioms KIP126.Synthetic.Bockstein.normalizedPreSS_Z_succ
#print axioms KIP126.Synthetic.Bockstein.normalizedPreSS_B_succ
#print axioms KIP126.Classical.Adams.adamsTowerInduced_isIso
#print axioms KIP126.Classical.Adams.adamsLayerInduced_isIso
#print axioms KIP126.Classical.Adams.adamsTowerHomInduced_bijective
#print axioms KIP126.Classical.Adams.adamsE1Induced_bijective
#print axioms KIP126.Classical.Adams.adamsE1Induced_mem_cycles_iff
#print axioms KIP126.Classical.Adams.adamsE1Induced_mem_boundaries_iff
#print axioms KIP126.Classical.Adams.adamsCycleInduced_bijective
#print axioms KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff
#print axioms KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.I_comp
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.I_range_eq
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.JToPage_I_zero
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.JToPage_eq_zero_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_zero_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.I_image_zero_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.I_K_zero
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.cycle_of_lift
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differential_lift_boundary
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.differential_range_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.pageIso_π
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.projection_surjective
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_comparison
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_π_eq_zero_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_kernel
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_range_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_π_range_iff
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_image
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_image_of_target_eq
#print axioms KIP126.Core.SpectralSequence.subobject_mem_iff_of_inverse
#print axioms KIP126.Core.SpectralSequence.subobject_quotient_iso_of_linearEquiv
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_comp
#print axioms KIP126.StableHomotopy.TowerSpectralSequence.internalD_transport

#print axioms KIP126.StableHomotopy.TowerSpectralSequence.sequence
#print axioms KIP126.Synthetic.Bockstein.normalizedSequence
#print axioms KIP126.Synthetic.Bockstein.normalizedAdamsSS

run_cmd do
  let declarations := #[
    ``KIP126.StableHomotopy.TowerSpectralSequence.sequence,
    ``KIP126.Synthetic.Bockstein.normalizedSequence,
    ``KIP126.Synthetic.Bockstein.normalizedAdamsSS,
    ``KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists,
    ``KIP126.Synthetic.SpectralSequence.exists_weightLiftRepresentative,
    ``KIP126.Classical.Adams.TowerDetection.exists_liftRepresentative,
    ``KIP126.Synthetic.Bockstein.normalizedPreSS_d_comp_d,
    ``KIP126.StableHomotopy.TowerSpectralSequence.preSS_d_comp_d,
    ``KIP126.StableHomotopy.SequentialHomotopyLimit.π_step,
    ``KIP126.StableHomotopy.SequentialHomotopyLimit.isZero_iff,
    ``KIP126.StableHomotopy.InverseSequence.toDescendingTower_layer_isZero,
    ``KIP126.StableHomotopy.TowerSpectralSequence.preSS_Z_succ,
    ``KIP126.StableHomotopy.TowerSpectralSequence.preSS_B_succ,
    ``KIP126.Synthetic.Bockstein.normalizedPreSS_Z_succ,
    ``KIP126.Synthetic.Bockstein.normalizedPreSS_B_succ,
    ``KIP126.Classical.Adams.adamsTowerInduced_isIso,
    ``KIP126.Classical.Adams.adamsLayerInduced_isIso,
    ``KIP126.Classical.Adams.adamsTowerHomInduced_bijective,
    ``KIP126.Classical.Adams.adamsE1Induced_bijective,
    ``KIP126.Classical.Adams.adamsE1Induced_mem_cycles_iff,
    ``KIP126.Classical.Adams.adamsE1Induced_mem_boundaries_iff,
    ``KIP126.Classical.Adams.adamsCycleInduced_bijective,
    ``KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff,
    ``KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.I_comp,
    ``KIP126.StableHomotopy.TowerSpectralSequence.I_range_eq,
    ``KIP126.StableHomotopy.TowerSpectralSequence.JToPage_I_zero,
    ``KIP126.StableHomotopy.TowerSpectralSequence.JToPage_eq_zero_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_zero_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.I_image_zero_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.I_K_zero,
    ``KIP126.StableHomotopy.TowerSpectralSequence.cycle_of_lift,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differential_lift_boundary,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differential_range_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.pageIso_π,
    ``KIP126.StableHomotopy.TowerSpectralSequence.projection_surjective,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_comparison,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_π_eq_zero_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_kernel,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_range_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_π_range_iff,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_image,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_image_of_target_eq,
    ``KIP126.Core.SpectralSequence.subobject_mem_iff_of_inverse,
    ``KIP126.Core.SpectralSequence.subobject_quotient_iso_of_linearEquiv,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_comp,
    ``KIP126.StableHomotopy.TowerSpectralSequence.internalD_transport,
    ``KIP126.StableHomotopy.DescendingTower.map_self,
    ``KIP126.StableHomotopy.DescendingTower.map_succ,
    ``KIP126.StableHomotopy.DescendingTower.map_adjacent,
    ``KIP126.StableHomotopy.DescendingTower.map_comp,
    ``KIP126.StableHomotopy.InverseSequence.toDescendingTower_map_nonpos,
    ``KIP126.StableHomotopy.TowerSpectralSequence.J_mem_cycles,
    ``KIP126.StableHomotopy.TowerSpectralSequence.cycles_one,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundaries_one,
    ``KIP126.StableHomotopy.TowerSpectralSequence.cycles_antitone,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundaries_monotone,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundaries_le_cycles,
    ``KIP126.StableHomotopy.TowerSpectralSequence.cycleSubmodule_antitone,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundarySubmodule_monotone,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundarySubmodule_le_cycle,
    ``KIP126.StableHomotopy.TowerSpectralSequence.JToPage_eq,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_of_lift,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_eq_zero_of_K,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_add,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differentialValue_smul,
    ``KIP126.StableHomotopy.TowerSpectralSequence.boundaries_le_differential_ker,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differential_JToPage,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differential_comp,
    ``KIP126.StableHomotopy.TowerSpectralSequence.firstPageProjection_eq_inv,
    ``KIP126.StableHomotopy.TowerSpectralSequence.firstPageIso_projection,
    ``KIP126.StableHomotopy.TowerSpectralSequence.ssData,
    ``KIP126.StableHomotopy.TowerSpectralSequence.pageIso,
    ``KIP126.StableHomotopy.TowerSpectralSequence.firstPageIso,
    ``KIP126.StableHomotopy.TowerSpectralSequence.differential]
  for name in declarations do
    let axioms ← liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Tower migration {name} depends on forbidden axiom {axiomName}"
  for moduleName in (← getEnv).allImportedModuleNames do
    if (`KIPBase).isPrefixOf moduleName ||
        (`KIP126.Interface).isPrefixOf moduleName ||
        (`KIP126.Main).isPrefixOf moduleName ||
        (`KIP126.LinProgram).isPrefixOf moduleName then
      throwError "Tower migration crosses a foundation boundary: {moduleName}"
