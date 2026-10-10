import KIP126.Def.StableHomotopy.Implementation.Data
import KIP126.Def.Kervaire.Route.Tools.GeneralizedLeibniz
import KIP126.Def.Kervaire.Route.Tools.GeneralizedMahowald
import KIP126.Def.Kervaire.Route.Tools.PageExtensionStretching
import Lean.Elab.Command

/-! Foundation and paper-tool statements must not consume computed facts or
stage axioms. Defining a law is not a proof that the chosen model satisfies it. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def.AdamsE2).isPrefixOf mod then
      throwError "foundation/paper-tool statements import a computation or stage input: {mod}"
  for law in [``KIP126.Kervaire.Route.Tools.GeneralizedLeibnizLaw,
      ``KIP126.Kervaire.Route.Tools.GeneralizedMahowaldLaw,
      ``KIP126.Kervaire.Route.Tools.FinitePageExtensionStretchingLaw] do
    let some (.defnInfo _) := env.find? law
      | throwError "paper obligation must be a proposition definition, not an axiom/theorem: {law}"
    for a in ← liftCoreM (collectAxioms law) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "paper statement acquired an unproved input: {law}: {a}"
