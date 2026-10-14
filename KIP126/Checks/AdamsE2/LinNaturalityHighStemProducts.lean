module

public import KIP126.LinProgram.Certificates.Products.Naturality462481
public import Lean.Elab.Command

@[expose] public section


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native quotient relation imported a model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.NaturalityHighStemProducts.map_relation_mem,
      ``KIP126.LinE2.NaturalityHighStemProducts.h0_relation_mem,
      ``KIP126.LinE2.NaturalityHighStemProducts.native_map_column0,
      ``KIP126.LinE2.NaturalityHighStemProducts.native_h0_product_zero,
      ``KIP126.LinE2.NaturalityHighStemProducts.ancestor_relation_mem,
      ``KIP126.LinE2.NaturalityHighStemProducts.native_ancestor_product] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected native quotient relation axiom {decl}: {ax}"

open KIP126.LinE2
example : True := by
  fail_if_success
    have : projection (monomialOfString "24,1,189,1") =
        projection (monomialOfString "7,2,279,1") := by
      exact NaturalityHighStemProducts.native_map_column0
  fail_if_success
    have : projection (monomialOfString "0,2,519,1") = 0 := by
      exact NaturalityHighStemProducts.native_h0_product_zero
  trivial

#print axioms KIP126.LinE2.NaturalityHighStemProducts.native_map_column0
#print axioms KIP126.LinE2.NaturalityHighStemProducts.native_h0_product_zero

#print axioms KIP126.LinE2.NaturalityHighStemProducts.native_ancestor_product
