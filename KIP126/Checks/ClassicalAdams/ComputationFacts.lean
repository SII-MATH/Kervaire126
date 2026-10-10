import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Literature.Near126
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Near126.Atom.record_eq,
      ``KIP126.Computation.Near126.atom,
      ``KIP126.Computation.Near126.d7Source,
      ``KIP126.Core.SpectralSequence.IsPageBoundary.zero,
      ``KIP126.Core.SpectralSequence.IsPageBoundary.add,
      ``KIP126.Core.SpectralSequence.IsPageBoundary.smul,
      ``KIP126.Core.SpectralSequence.IsPageBoundary.d_eq_zero,
      ``KIP126.Core.SpectralSequence.IsPageBoundary.isCycle,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.d_ne_zero,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.source_survives,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.target_survives,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.hit_target,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.not_all_zero,
      ``KIP126.Core.SpectralSequence.hasNonzeroDifferential_of_representatives,
      ``KIP126.Core.SpectralSequence.differentialVanishesOn_iff_not_hasNonzeroDifferential,
      ``KIP126.Core.SpectralSequence.NeverHit.not_hit] do
    for a in ← liftCoreM (collectAxioms decl) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected computation predicate/coordinate dependency: {decl}: {a}"
  for decl in [``KIP126.Computation.Near126.SphereDifferentialFacts.d3_x_126_6_ne_zero,
      ``KIP126.Computation.Near126.SphereSurvivalFacts.y_not_hit_on_page,
      ``KIP126.Computation.Near126.SphereBoundaryFacts.p_h2_is_d2_cycle,
      ``KIP126.Computation.Near126.SphereBoundaryFacts.q_h2_is_d2_cycle,
      ``KIP126.Computation.Near126.Sphere.d12_iff_differential,
      ``KIP126.Computation.Near126.SphereSurvivalFacts.c3_iff_not_d6,
      ``KIP126.Computation.Near126.SphereSurvivalFacts.hit_t_iff_d12] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer
      (logical ++ [``KIP126.Classical.Adams.standardFoundation,
        ``KIP126.Classical.Adams.linE2Presentation]) decl
      "unexpected fixed-sphere fact dependency"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Main.Challenge).isPrefixOf m then
      throwError "unexpected computation-facts import: {m}"

#print axioms KIP126.Computation.Near126.Atom.record_eq
#print axioms KIP126.Computation.Near126.SphereDifferentialFacts.d3_x_126_6_ne_zero
#print axioms KIP126.Computation.Near126.SphereSurvivalFacts.y_not_hit_on_page
