module

public import KIP126.LinProgram.Certificates.Products.Trial152097
public import Lean.Elab.Command

@[expose] public section


/-! The actual fixed-data quotient products are closed proofs. These checks
reject producer/consumer imports and any axiom outside Lean's logical basis. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "closed quotient certificate imported an actual-model assumption: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.RelationCatalogue.rawLine_mem_of_join,
      ``KIP126.LinE2.ReplayProducts.relation26_mem,
      ``KIP126.LinE2.ReplayProducts.relation188_mem,
      ``KIP126.LinE2.ReplayProducts.relation190_mem,
      ``KIP126.LinE2.ReplayProducts.source_product_zero,
      ``KIP126.LinE2.ReplayProducts.target_product,
      ``KIP126.LinE2.ReplayProducts.native_source_product_zero,
      ``KIP126.LinE2.ReplayProducts.native_target_product] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in fixed quotient certificate {decl}: {ax}"

open KIP126.LinE2

set_option maxRecDepth 100000 in
example : True := by
  fail_if_success
    have : "not a relation" ∈ RawData.relations := by
      lin_relation 0 "not a relation"
  fail_if_success
    have : "10,1,13,1;2,1,32,1" ∈ RawData.relations := by
      lin_relation 0 "1,1,9,1;0,1,10,1"
  trivial

example : True := by
  fail_if_success
    have : projection (monomialOfString "1,1,9,1,13,1") =
        projection (monomialOfString "0,2,36,1") := by
      exact ReplayProducts.native_target_product
  trivial

#print axioms KIP126.LinE2.ReplayProducts.native_source_product_zero
#print axioms KIP126.LinE2.ReplayProducts.native_target_product
