module

public import KIP126.Def.SpectralSequence.Computation.State.Proofs
public import KIP126.LinProgram.Interpretation.Branch.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! The replay kernel operates on actual spectral-sequence pages and equations.
No database diagnostic or generated algebra certificate proves its premises. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "replay kernel imported a stage producer or consumer: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Core.SpectralSequence.SSData.pageπ_eq_zero_iff,
      ``KIP126.Core.SpectralSequence.SSData.page_eq_of_early_page_eq,
      ``KIP126.Core.SpectralSequence.RepresentsOnPage.unique,
      ``KIP126.Core.SpectralSequence.RepresentsOnPage.eq_zero_iff_isBoundaryBy,
      ``KIP126.Core.SpectralSequence.HasDifferential.isBoundaryBy_of_source_zero,
      ``KIP126.Core.SpectralSequence.not_hasDifferential_zero_of_not_isBoundaryBy,
      ``KIP126.Core.SpectralSequence.ReachesPage.hasDifferential_zero,
      ``KIP126.Core.SpectralSequence.ReachesPage.survives_of_not_isBoundaryBy,
      ``KIP126.Core.SpectralSequence.hasDifferential_zero_of_excluded_target,
      ``KIP126.Computation.LinProofs.Branch.CandidateElimination.sound,
      ``KIP126.Computation.LinProofs.Branch.CandidateElimination.sound_nil,
      ``KIP126.Computation.LinProofs.Branch.CandidateExhaustion.sound,
      ``KIP126.Computation.LinProofs.Branch.EquationConflict.sound,
      ``KIP126.Computation.LinProofs.Branch.TrialRefuted.of_zero_source,
      ``KIP126.Computation.LinProofs.Branch.TrialRefuted.of_contradiction_cons] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in actual-object replay rule {decl}: {ax}"

#print axioms KIP126.Core.SpectralSequence.RepresentsOnPage.eq_zero_iff_isBoundaryBy
#print axioms KIP126.Core.SpectralSequence.hasDifferential_zero_of_excluded_target
#print axioms KIP126.Computation.LinProofs.Branch.CandidateElimination.sound_nil

/- The exact zero-source obstruction printed by retained trial 152097.
This works on the supplied actual sequence. It proves neither the earlier
boundary exclusion, the E₄ Leibniz premise, nor the candidate coverage needed
to conclude root deduction 152098. -/
open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence in
example {R : Type*} [Ring R]
    (E : SpectralSequence (ModuleCat R) (ℤ × ℤ)) (z : E.Page 2 (9, 47))
    (hz : ¬ IsBoundaryBy E 3 (9, 47) z) :
    ¬ HasDifferential E 4 (5, 44) (9, 47) 0 z :=
  not_hasDifferential_zero_of_not_isBoundaryBy (by decide) hz

#print axioms KIP126.Core.SpectralSequence.HasDifferential.isBoundaryBy_of_source_zero
#print axioms KIP126.Computation.LinProofs.Branch.TrialRefuted.of_zero_source
