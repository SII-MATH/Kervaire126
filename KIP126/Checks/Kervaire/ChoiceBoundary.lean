import KIP126.Main.Solution.DifferentialReduction.Conclusion
import KIP126.Main.Solution.ChoiceIndependence.any_choice_criterion
import Lean.Elab.Command

/-! Check the active paper propositions and the conditional final inference;
its premises remain pending. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [``KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence,
      ``KIP126.Solution.Near126.C3NotC5.c3_excludes_c5,
      ``KIP126.Solution.Near126.Thm7_3BJMBX.any_choice_criterion] do
    let some (.defnInfo _) := env.find? n
      | throwError "pending paper proposition must not be an unconditional theorem: {n}"
  for a in ← liftCoreM (collectAxioms ``KIP126.Main.Solution.permanent_of_propositions) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "conditional final inference acquired an assumption: {a}"
