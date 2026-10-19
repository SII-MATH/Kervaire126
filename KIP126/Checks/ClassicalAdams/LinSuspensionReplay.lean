module

public import KIP126.Def.ClassicalAdams.Suspension.Internal.Proofs
public import KIP126.Def.SpectralSequence.Computation.Morphism.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! These generic comparisons are derived from the actual supplied tower
squares. They must not inherit a fixed-model admission or a computation delivery. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic suspension comparison imported a stage or native-data dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Classical.Adams.Suspension.TowerComparison.desuspend_adamsI,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspend_adamsJ,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspend_adamsK,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspendFirstPage_mem_cycles,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspendFirstPage_mem_boundaries,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspendPage_differential,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspendInternalPage_d,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.desuspendTwiceInternalPage_d,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.hasDifferential_desuspendTwice,
      ``KIP126.Core.SpectralSequence.SSDataMorphism.representsOnPage_reindexed,
      ``KIP126.Core.SpectralSequence.SSDataMorphism.hasDifferential_reindexed,
      ``KIP126.Core.SpectralSequence.SpectralSequenceMorphism.representsOnPage,
      ``KIP126.Core.SpectralSequence.SpectralSequenceMorphism.hasDifferential] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in generic suspension/reindexing result {decl}: {ax}"

#print axioms KIP126.Classical.Adams.Suspension.TowerComparison.desuspend_adamsK
#print axioms KIP126.Core.SpectralSequence.SSDataMorphism.representsOnPage_reindexed

#print axioms KIP126.Core.SpectralSequence.SSDataMorphism.hasDifferential_reindexed

#print axioms KIP126.Classical.Adams.Suspension.TowerComparison.desuspendPage_differential

#print axioms KIP126.Classical.Adams.Suspension.TowerComparison.hasDifferential_desuspendTwice
