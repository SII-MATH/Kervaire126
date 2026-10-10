import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs
import KIP126.Def.StageInput.Foundation
import Lean.Elab.Command

/-! Audit the actual layer comparison and homology-zero tower maps.
The generic declarations must not depend on fixed foundation, Milnor,
Lin, or native-computation axioms, nor reverse-import an SS adapter. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsFiberTriangle_distinguished,
      ``KIP126.Classical.Adams.fiberι_comp_eq_zero,
      ``KIP126.Classical.Adams.cofiberFiberIso,
      ``KIP126.Classical.Adams.cofiberFiberIso_ι,
      ``KIP126.Classical.Adams.adamsLayerTriangleIso,
      ``KIP126.Classical.Adams.adamsLayerIso,
      ``KIP126.Classical.Adams.adamsLayerIso_ι,
      ``KIP126.Classical.Adams.adamsLayerIso_δ,
      ``KIP126.Classical.Adams.adamsE1HomologyEquiv,
      ``KIP126.Classical.Adams.adamsE1HomologyEquiv_J,
      ``KIP126.Classical.Adams.adamsPageOneEquiv,
      ``KIP126.Classical.Adams.adamsPageOneHomologyEquiv,
      ``KIP126.Classical.Adams.adamsPageOneHomologyEquiv_mkQ,
      ``KIP126.StableHomotopy.Cohomology.mod2FreeAction_unit,
      ``KIP126.StableHomotopy.Cohomology.mod2_adamsTowerStep_eq_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2_adamsTowerStep_homology_eq_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2_adamsTowerMap_eq_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2_homology_eq_zero_of_tower_lift] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected layer comparison dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected layer comparison import: {m}"

/- The comparison specializes to the chosen sphere foundation without Milnor
coordinates or an independent page-comparison axiom. -/
open KIP126.Classical.Adams KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology in
noncomputable example (s : ℕ) (t : ℤ) :
    adamsPage standardFoundation.hf2.unit SphereSpectrum 1 (by decide) s t ≃ₗ[ℤ]
      Mod2Homology standardFoundation.hf2 (t - s)
        (adamsTower standardFoundation.hf2.unit SphereSpectrum s) :=
  adamsPageOneHomologyEquiv standardFoundation.hf2.unit SphereSpectrum s t

#print axioms KIP126.Classical.Adams.adamsPageOneHomologyEquiv
#print axioms KIP126.Classical.Adams.adamsLayerIso_δ
#print axioms KIP126.StableHomotopy.Cohomology.mod2_homology_eq_zero_of_tower_lift
