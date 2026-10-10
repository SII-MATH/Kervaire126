import KIP126.Def.Kervaire.Theta5.Proofs
import Lean.Elab.Command

/-! Generic transport in Def must not require project delivery or source packages. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf m || (`KIP126.Interface).isPrefixOf m then
      throwError "Def choice transport imports a project package: {m}"
  for n in [``KIP126.Kervaire.theta5_choice_independence,
      ``KIP126.Kervaire.bjm_bx_criterion_any_choice,
      ``KIP126.Kervaire.bjm_bx_criterion_any_choice_iff] do
    for a in ← liftCoreM (collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "generic transport acquired an unfinished or external proof: {n}: {a}"
