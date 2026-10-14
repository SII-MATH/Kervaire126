module

public import KIP126.Def.StableHomotopy.Context.CofiberExtension.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! The shifted-cofiber extension keeps the vanishing composite as an explicit
premise. It does not read the fixed model, any delivery, or native artifacts. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic cofiber extension imports an actual delivery or artifact: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.StableHomotopy.CofiberExtension.shiftedCofiberTriangle,
      ``KIP126.StableHomotopy.CofiberExtension.shiftedCofiberTriangle_distinguished,
      ``KIP126.StableHomotopy.CofiberExtension.sphereSixIso,
      ``KIP126.StableHomotopy.CofiberExtension.shiftFourIso,
      ``KIP126.StableHomotopy.CofiberExtension.cofiber_triangle_of_extension,
      ``KIP126.StableHomotopy.CofiberExtension.exists_eta_nu_cofiber_triangles,
      ``KIP126.StableHomotopy.CofiberExtension.exists_extension_of_shift_comp_zero,
      ``KIP126.StableHomotopy.CofiberExtension.exists_eta_nu_extension] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in shifted cofiber extension {decl}: {ax}"

#print axioms KIP126.StableHomotopy.CofiberExtension.exists_extension_of_shift_comp_zero
#print axioms KIP126.StableHomotopy.CofiberExtension.exists_eta_nu_extension

#print axioms KIP126.StableHomotopy.CofiberExtension.cofiber_triangle_of_extension

#print axioms KIP126.StableHomotopy.CofiberExtension.exists_eta_nu_cofiber_triangles
