module

public import KIP126.LinProgram.Model.ModulePresentation.Maps
public import KIP126.LinProgram.Model.Modules
public import Lean.Elab.Command

@[expose] public section


open KIP126.LinModule KIP126.LinModule.Presentation

/-- These specializations retain all relations as explicit obligations;
they do not provide any actual map's images or certify relation vanishing. -/
example (g : Ceta.Generator → KIP126.LinE2.E2)
    (hrel : ∀ code ∈ RawData.Ceta.relations, evaluateRelation g code = 0) :
    ∃! f : Ceta.Model →ₗ[KIP126.LinE2.E2] KIP126.LinE2.E2,
      ∀ i, f (Ceta.generator i) = g i :=
  existsUnique_desc g _ hrel

example (g : CWNuEta.Generator → Ceta.Model)
    (hrel : ∀ code ∈ RawData.CWNuEta.relations, evaluateRelation g code = 0) :
    ∃! f : CWNuEta.Model →ₗ[KIP126.LinE2.E2] Ceta.Model,
      ∀ i, f (CWNuEta.generator i) = g i :=
  existsUnique_desc g _ hrel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod || mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native module descent imports an actual model, delivery or basis premise: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``evaluateRelation, ``linearCombination_ofPowers,
      ``linearCombination_monomialVector, ``linearCombination_relationVector,
      ``definingSubmodule_le_ker, ``desc, ``desc_projection, ``desc_generator,
      ``desc_ofPowers, ``desc_monomialVector, ``desc_relationVector,
      ``hom_ext, ``desc_unique, ``existsUnique_desc] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected module descent axiom: {decl}: {ax}"

#print axioms KIP126.LinModule.Presentation.desc
#print axioms KIP126.LinModule.Presentation.existsUnique_desc
