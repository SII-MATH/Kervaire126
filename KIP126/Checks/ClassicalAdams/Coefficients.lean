import KIP126.Def.ClassicalAdams.Coefficients.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Proofs
import Lean.Elab.Command

/-! Scalar structures and their linear maps must be derived from the explicit
ring and additive tensor, not selected by a fixed or computational axiom. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.mod2Unit_add_self,
      ``KIP126.StableHomotopy.Cohomology.mod2_id_add_self,
      ``KIP126.StableHomotopy.Cohomology.mod2Free_id_add_self,
      ``KIP126.StableHomotopy.Cohomology.mod2Homology_two_nsmul_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2Cohomology_two_nsmul_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2HF2Homotopy_two_nsmul_zero,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyModule,
      ``KIP126.StableHomotopy.Cohomology.mod2CohomologyModule,
      ``KIP126.StableHomotopy.Cohomology.mod2HF2HomotopyModule,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyModule_eq,
      ``KIP126.StableHomotopy.Cohomology.mod2Pi0LinearEquiv,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounitF2,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounitF2_apply,
      ``KIP126.StableHomotopy.Cohomology.cooperationDiagonalF2,
      ``KIP126.StableHomotopy.Cohomology.cooperationDiagonalF2_apply,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyF2Functor,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyF2Map_apply,
      ``KIP126.Classical.Adams.adamsE1_two_nsmul_zero,
      ``KIP126.Classical.Adams.adamsPage_two_nsmul_zero,
      ``KIP126.Classical.Adams.adamsInternalPage_two_nsmul_zero,
      ``KIP126.Classical.Adams.adamsPageF2Module,
      ``KIP126.Classical.Adams.adamsInternalPageF2Module,
      ``KIP126.Classical.Adams.adamsDifferentialF2_apply,
      ``KIP126.Classical.Adams.adamsInternalDifferentialF2_apply,
      ``KIP126.Classical.Adams.adamsInternalDifferentialF2_comp,
      ``KIP126.Classical.Adams.adamsPageOneHomologyF2Equiv,
      ``KIP126.Classical.Adams.adamsPageOneHomologyF2Equiv_apply,
      ``KIP126.Classical.Adams.adamsHomologyKernelF2Equiv,
      ``KIP126.Classical.Adams.adamsHomologySplitF2Equiv,
      ``KIP126.Classical.Adams.adamsHomologySplitF2Equiv_apply,
      ``KIP126.Classical.Adams.adamsHomologyKernelF2Equiv_apply] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected mod-two coefficient dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected mod-two coefficient import: {m}"

/- The internal finite-page scalars can be used locally without replacing
the existing integer-module SSData construction. -/
open CategoryTheory KIP126.Classical.Adams KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology in
example {C : Type*} [StableHomotopyCategory C] [MonoidalPreadditive C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    (R : Mod2RingStructure H) (X : C) (r s t : ℤ)
    (x : (adamsTowerInternalSpectralSequence H.unit X).Page r (s, t)) :
    letI := adamsInternalPageF2Module H R X r s t
    (1 : ZMod 2) • x = x := by
  letI := adamsInternalPageF2Module H R X r s t
  exact one_smul _ _

#print axioms KIP126.StableHomotopy.Cohomology.mod2HomologyModule
#print axioms KIP126.Classical.Adams.adamsInternalPageF2Module
#print axioms KIP126.Classical.Adams.adamsHomologyKernelF2Equiv
