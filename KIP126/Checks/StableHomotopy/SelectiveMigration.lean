import KIP126.Def.Comparison.ClassicalSynthetic.RealizationWeights.Proofs
import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Detection.Proofs
import KIP126.Def.Solution.Toda
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
import KIP126.Def.ClassicalAdams.Convergence.Tower.Raw.Proofs
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Proofs
import KIP126.Def.StableHomotopy.Toda.Law.Proofs
import Lean.Elab.Command

/-! Full dependency audit for the remaining selective proof transfers.
All targets use existing mathematical objects. Any nonstandard axiom,
including a sorry introduced in an elaborated parameter type, is rejected. -/

open Lean Elab Command

#print axioms KIP126.Classical.Adams.adamsTowerHomInduced_cast
#print axioms KIP126.Classical.Adams.adamsPageInduced_JToPage
#print axioms KIP126.Classical.Adams.adamsPageInduced_differential
#print axioms KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule
#print axioms KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule
#print axioms KIP126.Classical.Adams.adamsTowerSSDataMorphism_exists
#print axioms KIP126.Classical.Adams.adamsTowerSSDataMorphism_page_comparison
#print axioms KIP126.Classical.Adams.adamsTowerSSDataMorphism_internalD
#print axioms KIP126.Classical.Adams.adamsTowerSSDataMorphism_internalD_reindex
#print axioms KIP126.Classical.Adams.adamsTowerSpectralSequenceMorphism_exists
#print axioms KIP126.Classical.Adams.adamsPageInduced_mkQ
#print axioms KIP126.Classical.Adams.adamsInternalE2Induced_coordinates
#print axioms KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential
#print axioms KIP126.Classical.Adams.adamsHomotopyFiltrationSubmodule_decreasing
#print axioms KIP126.StableHomotopy.homotopyDesuspend_bijective
#print axioms KIP126.StableHomotopy.homotopyDesuspend_postcompose
#print axioms KIP126.StableHomotopy.Toda.precompose
#print axioms KIP126.StableHomotopy.Toda.postcompose
#print axioms KIP126.StableHomotopy.Toda.absorb_first
#print axioms KIP126.StableHomotopy.Toda.absorb_last
#print axioms KIP126.StableHomotopy.Toda.shuffle_iff
#print axioms KIP126.StableHomotopy.Toda.suspension_iff
#print axioms KIP126.StableHomotopy.Toda.map
#print axioms KIP126.StableHomotopy.Toda.tensor_right
#print axioms KIP126.StableHomotopy.Toda.tensor_left
#print axioms KIP126.Comparison.ClassicalSynthetic.RealizationTower.towerMap_naturality
#print axioms KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_cycles
#print axioms KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_boundaries

#print axioms KIP126.Def.Solution.todaNaturalityInterface
#print axioms KIP126.Def.Solution.todaFunctorInterface
#print axioms KIP126.Def.Solution.todaTensorInterface

#print axioms KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison.unique
#print axioms KIP126.Comparison.ClassicalSynthetic.detects_unique_of_next_filtration_zero
#print axioms KIP126.Comparison.ClassicalSynthetic.firstQuotient_next_filtration_zero_of_range
#print axioms KIP126.Comparison.ClassicalSynthetic.firstQuotient_inverse_eq_of_detection

run_cmd do
  let declarations := #[
    ``KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison.unique,
    ``KIP126.Comparison.ClassicalSynthetic.detects_unique_of_next_filtration_zero,
    ``KIP126.Comparison.ClassicalSynthetic.firstQuotient_next_filtration_zero_of_range,
    ``KIP126.Comparison.ClassicalSynthetic.firstQuotient_inverse_eq_of_detection,
    ``KIP126.Def.Solution.todaNaturalityInterface,
    ``KIP126.Def.Solution.todaFunctorInterface,
    ``KIP126.Def.Solution.todaTensorInterface,
    ``KIP126.Classical.Adams.adamsTowerHomInduced_cast,
    ``KIP126.Classical.Adams.adamsPageInduced_JToPage,
    ``KIP126.Classical.Adams.adamsPageInduced_differential,
    ``KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule,
    ``KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule,
    ``KIP126.Classical.Adams.adamsTowerSSDataMorphism_exists,
    ``KIP126.Classical.Adams.adamsTowerSSDataMorphism_page_comparison,
    ``KIP126.Classical.Adams.adamsTowerSSDataMorphism_internalD,
    ``KIP126.Classical.Adams.adamsTowerSSDataMorphism_internalD_reindex,
    ``KIP126.Classical.Adams.adamsTowerSpectralSequenceMorphism_exists,
    ``KIP126.Classical.Adams.adamsPageInduced_mkQ,
    ``KIP126.Classical.Adams.adamsInternalE2Induced_coordinates,
    ``KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential,
    ``KIP126.Classical.Adams.adamsHomotopyFiltrationSubmodule_decreasing,
    ``KIP126.StableHomotopy.homotopyDesuspend_bijective,
    ``KIP126.StableHomotopy.homotopyDesuspend_postcompose,
    ``KIP126.StableHomotopy.Toda.precompose,
    ``KIP126.StableHomotopy.Toda.postcompose,
    ``KIP126.StableHomotopy.Toda.absorb_first,
    ``KIP126.StableHomotopy.Toda.absorb_last,
    ``KIP126.StableHomotopy.Toda.shuffle_iff,
    ``KIP126.StableHomotopy.Toda.suspension_iff,
    ``KIP126.StableHomotopy.Toda.map,
    ``KIP126.StableHomotopy.Toda.tensor_right,
    ``KIP126.StableHomotopy.Toda.tensor_left,
    ``KIP126.Comparison.ClassicalSynthetic.RealizationTower.towerMap_naturality,
    ``KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_cycles,
    ``KIP126.Comparison.ClassicalSynthetic.RealizationTower.e1Map_mem_boundaries]
  for name in declarations do
    let axioms ← liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Selective migration {name} depends on forbidden axiom {axiomName}"
  for moduleName in (← getEnv).allImportedModuleNames do
    if (`KIPBase).isPrefixOf moduleName ||
        (`KIP126.Interface).isPrefixOf moduleName ||
        (`KIP126.Main).isPrefixOf moduleName ||
        (`KIP126.LinProgram).isPrefixOf moduleName then
      throwError "Selective migration crosses a foundation boundary: {moduleName}"
