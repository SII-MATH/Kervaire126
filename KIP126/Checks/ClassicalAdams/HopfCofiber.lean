import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Literature.Near126.HopfCofiber.Fixed.Data
import KIP126.Main.Solution.Literature.HopfCofiber.Proofs
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Classical.Adams.adamsUnit_naturality,
      ``KIP126.Classical.Adams.fiberMap_ι,
      ``KIP126.Classical.Adams.adamsTowerInduced_step,
      ``KIP126.Classical.Adams.adamsE1Induced_mem_cycles,
      ``KIP126.Classical.Adams.adamsE1Induced_mem_boundaries,
      ``KIP126.Classical.Adams.adamsInternalE2Induced,
      ``KIP126.Classical.Adams.adamsPageInduced_mkQ,
      ``KIP126.Classical.Adams.adamsInternalE2Induced_coordinates] do
    for a in ← liftCoreM (collectAxioms decl) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected tower naturality assumption: {decl}: {a}"
  for decl in [``KIP126.Classical.Adams.sphereMapCofiberAdams,
      ``KIP126.Classical.Adams.sphereFiltrationOneClass,
      ``KIP126.Classical.Adams.sphereMapCofiber_first_zero,
      ``KIP126.Classical.Adams.sphereMapCofiber_cells_zero,
      ``KIP126.Classical.Adams.sphereMapCofiberBottomE2,
      ``KIP126.Classical.Adams.sphereMapCofiberTopE2,
      ``KIP126.Classical.Adams.sphereMapCofiberInclusionTower_step] do
    for a in ← liftCoreM (collectAxioms decl) do
      unless KIP126.Checks.AxiomInputs.allows (logical ++ [``KIP126.Classical.Adams.standardFoundation]) a do
        throwError "unexpected sphere cofiber assumption: {decl}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`KIP126.Main.Challenge).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected Hopf cofiber import: {m}"

#print axioms KIP126.Classical.Adams.adamsTowerInduced_step
#print axioms KIP126.Classical.Adams.sphereFiltrationOneClass
#print axioms KIP126.Classical.Adams.sphereMapCofiberAdams
