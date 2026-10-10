import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Boundary.Proofs
import Lean.Elab.Command

/-! The non-boundary calculation is pure algebra and kernel-checked.
It must not acquire Adams, Lin-table, or project-axiom dependencies. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Steenrod.Milnor.xiOneProjection,
      ``KIP126.Steenrod.Milnor.h6SquarePureDetector,
      ``KIP126.Steenrod.Milnor.h6SquareDetector,
      ``KIP126.Steenrod.Milnor.xiOneProjection_X,
      ``KIP126.Steenrod.Milnor.xiOneProjection_xi,
      ``KIP126.Steenrod.Milnor.xiOneProjection_coproductGenerator,
      ``KIP126.Steenrod.Milnor.xiOneProjection_split_X,
      ``KIP126.Steenrod.Milnor.xiOneProjection_insertLeft,
      ``KIP126.Steenrod.Milnor.xiOneProjection_insertRight,
      ``KIP126.Steenrod.Milnor.h6SquarePureDetector_apply,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_square,
      ``KIP126.Steenrod.Milnor.h6SquarePureDetector_rename,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_insertLeft,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_insertRight,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_differential,
      ``KIP126.Steenrod.Milnor.binaryChooseParity,
      ``KIP126.Steenrod.Milnor.binaryChooseParity_eq,
      ``KIP126.Steenrod.Milnor.h6Square_binary_parity,
      ``KIP126.Steenrod.Milnor.h6Square_binomial_parity,
      ``KIP126.Steenrod.Milnor.h6Square_binomial_coefficient,
      ``KIP126.Steenrod.Milnor.h6SquarePureDetector_binomial,
      ``KIP126.Steenrod.Milnor.xiOneProjection_split_monomial_high,
      ``KIP126.Steenrod.Milnor.singleSlot_exponents_eq_two,
      ``KIP126.Steenrod.Milnor.xiOneProjection_split_monomial_two,
      ``KIP126.Steenrod.Milnor.singleSlot_two_weight,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_differential_monomial,
      ``KIP126.Steenrod.Milnor.h6SquareDetector_differential_zero,
      ``KIP126.Steenrod.Milnor.h6SquareCochain_not_boundary] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Milnor square non-boundary dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams).isPrefixOf m ||
        (`KIP126.Def.StableHomotopy).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m ||
        (`KIP126.LinProgram).isPrefixOf m then
      throwError "unexpected pure-cobar non-boundary import: {m}"

#print axioms KIP126.Steenrod.Milnor.h6Square_binary_parity
#print axioms KIP126.Steenrod.Milnor.h6SquareCochain_not_boundary
