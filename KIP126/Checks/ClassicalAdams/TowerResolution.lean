import KIP126.Def.ClassicalAdams.TowerResolution.Sphere.Proofs
import KIP126.Def.StageInput.Foundation
import Lean.Elab.Command

/-! The first differential must be proved from the tower, not assumed through
Milnor coordinates, Lin data, a fixed foundation, or an SS adapter. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsResolutionConnecting,
      ``KIP126.Classical.Adams.adamsResolutionTriangle_distinguished,
      ``KIP126.Classical.Adams.adamsResolutionBoundary,
      ``KIP126.Classical.Adams.adamsResolutionDifferential,
      ``KIP126.Classical.Adams.adamsK_eq_resolutionBoundary,
      ``KIP126.Classical.Adams.adamsCycleLift_one,
      ``KIP126.Classical.Adams.adamsDifferential_one,
      ``KIP126.Classical.Adams.adamsPageD_one,
      ``KIP126.Classical.Adams.adamsPageD_one_homology,
      ``KIP126.Classical.Adams.adamsResolutionDifferential_comp,
      ``KIP126.Classical.Adams.sphereFirstDifferential_homology] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected resolution differential dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected resolution differential import: {m}"

/- The theorem applies to the fixed sphere without a Milnor-coordinate input. -/
open KIP126.Classical.Adams KIP126.StableHomotopy in
example (s t : ℕ)
    (x : adamsPage standardFoundation.hf2.unit SphereSpectrum 1 (by decide) s t) :
    adamsPageOneHomologyEquiv standardFoundation.hf2.unit SphereSpectrum (s + 1) t
      (sphereFirstDifferential standardFoundation.hf2 s t x) =
        adamsResolutionDifferential standardFoundation.hf2.unit SphereSpectrum s t
          (adamsPageOneHomologyEquiv standardFoundation.hf2.unit SphereSpectrum s t x) :=
  sphereFirstDifferential_homology standardFoundation.hf2 s t x

#print axioms KIP126.Classical.Adams.adamsPageD_one_homology
#print axioms KIP126.Classical.Adams.adamsResolutionDifferential_comp
#print axioms KIP126.Classical.Adams.sphereFirstDifferential_homology
