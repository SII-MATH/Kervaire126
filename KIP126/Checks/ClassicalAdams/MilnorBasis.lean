import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Elementary.Proofs
import Lean.Elab.Command

/-! The monomial basis and tensor conversion are proved below Adams pages.
The reduced-cooperation basis is a parameter, not a named existence axiom. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Steenrod.Milnor.augmentSlot_monomial,
      ``KIP126.Steenrod.Milnor.coeff_augmentSlot,
      ``KIP126.Steenrod.Milnor.augmentSlot_eq_zero_iff,
      ``KIP126.Steenrod.Milnor.mem_cochains_iff_monomials,
      ``KIP126.Steenrod.Milnor.cochains_map_coeff,
      ``KIP126.Steenrod.Milnor.cochainsMonomialEquiv,
      ``KIP126.Steenrod.Milnor.cochainsMonomialBasis,
      ``KIP126.Steenrod.Milnor.cochainsMonomialBasis_val,
      ``KIP126.Steenrod.Milnor.cochainsMonomialEquiv_monomial,
      ``KIP126.Steenrod.Milnor.weight_eq_sum_slotWeight,
      ``KIP126.Steenrod.Milnor.wordConsEquiv,
      ``KIP126.Steenrod.Milnor.cochainMonomialEquivWord,
      ``KIP126.Steenrod.Milnor.cochainsWordEquiv,
      ``KIP126.Steenrod.Milnor.cochainsWordEquiv_apply,
      ``KIP126.Steenrod.Milnor.wordTensorEquiv,
      ``KIP126.Steenrod.Milnor.wordTensorEquiv_single,
      ``KIP126.Steenrod.Milnor.emptyMilnorWord,
      ``KIP126.Steenrod.Milnor.h6PositiveMonomial,
      ``KIP126.Steenrod.Milnor.h6MilnorWord,
      ``KIP126.Steenrod.Milnor.h6SquareMilnorWord,
      ``KIP126.Steenrod.Milnor.cochainsWordEquiv_symm_single_val,
      ``KIP126.Steenrod.Milnor.h6MilnorWord_exponents,
      ``KIP126.Steenrod.Milnor.h6SquareMilnorWord_exponents,
      ``KIP126.Steenrod.Milnor.cochainsWordEquiv_h6,
      ``KIP126.Steenrod.Milnor.cochainsWordEquiv_h6Square,
      ``KIP126.StableHomotopy.Cohomology.reducedTensorMilnorWordEquiv_basis_single,
      ``KIP126.Steenrod.Milnor.differential,
      ``KIP126.Steenrod.Milnor.cup,
      ``KIP126.StableHomotopy.Cohomology.reducedTensorMilnorWordEquiv,
      ``KIP126.Steenrod.Milnor.slotWeight_eq_zero_iff,
      ``KIP126.Steenrod.Milnor.positiveMonomial_degree_pos,
      ``KIP126.Steenrod.Milnor.milnorMonomial_zero_eq,
      ``KIP126.Steenrod.Milnor.milnorMonomialEquivPositive,
      ``KIP126.Steenrod.Milnor.milnorZeroCoefficientsEquiv,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounit_surjective,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperations_zero_subsingleton,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounitF2_zero_bijective,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv_zero_coefficient,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv_of_ne,
      ``KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv_reduced_basis,
      ``KIP126.StableHomotopy.Cohomology.cooperation_linearMap_ext] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Milnor-basis dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerPages).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerDifferential).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerHomology).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerResolution).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected below-page Milnor-basis import: {m}"

#print axioms KIP126.Steenrod.Milnor.cochainsWordEquiv
#print axioms KIP126.StableHomotopy.Cohomology.reducedTensorMilnorWordEquiv
#print axioms KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv
#print axioms KIP126.StableHomotopy.Cohomology.cooperationMilnorEquiv_unit
