module

public import KIP126.LinProgram.Certificates.Naturality.Words200.Native
public import KIP126.LinProgram.Certificates.RelationCatalogue.Homogeneity
public import Lean.Elab.Command

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Native algebra certificate scope, double-degree rejection, and kernel trust.
No actual sphere presentation is imported or treated as proved. -/
namespace KIP126.Checks.LinNativeWords200
open KIP126.LinE2 KIP126.LinModule BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
attribute [local cbv_eval] generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.toNat?_eq_chars

-- x₁ and x₀² both have internal degree 2 but different filtration degrees.
example : RelationCatalogue.relationCheck "1,1;0,2" = false := by cbv
-- x₀ and x₁ both have filtration degree 1 but different internal degrees.
example : RelationCatalogue.relationCheck "0,1;1,1" = false := by cbv
-- Weighted degree, not ordinary exponent sum: (3,6) on both sides.
example : RelationCatalogue.relationCheck "1,3;0,2,2,1" = true := by cbv
-- The generic homogeneity test imposes no artificial t ≤ 261 bound.
example : RelationCatalogue.relationCheck "0,262" = true := by cbv

example : NaturalityWords200.entries.length = 15951 := NaturalityWords200.native_entry_count
example : NaturalityWords200.entries.map (fun e => e.source.id) = List.range' 2 15951 :=
  NaturalityWords200.native_source_ids
example (e : Entry) (he : e ∈ NaturalityWords200.entries) :
    NativeWordCertificate.evaluatePowers NativeWordCertificate.generatorImage (word e) =
      NativeWordCertificate.targetValue e := NaturalityWords200.entry_native_evaluate e he
example (code : String) (h : code ∈ KIP126.LinE2.RawData.relations) :
    ∃ d : ℕ × ℕ, MvPolynomial.IsWeightedHomogeneous generatorDegree (relationPolynomial code) d :=
  csv_relation_isWeightedHomogeneous code h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod then
      throwError "native algebra certificate imports actual-model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``RelationCatalogue.powers_homogeneous,
      ``RelationCatalogue.monomial_homogeneous, ``RelationCatalogue.relationCheck_sound,
      ``RelationCatalogue.relationCheck_eq_chars, ``RelationCatalogue.archivedChunks_check,
      ``csv_relation_isWeightedHomogeneous, ``NativeWordCertificate.check_sound_evaluate,
      ``NaturalityWords200.batch_relations_mem,
      ``NaturalityWords200.entry_native_evaluate, ``NaturalityWords200.zero_native_evaluate,
      ``NaturalityWords200.entry_truncate_compatible, ``NaturalityWords200.native_source_ids,
      ``NaturalityWords200.native_entry_count, ``SquareDetection.nativeIdeal_le_ker,
      ``SquareDetection.native_h6_square_ne_zero, ``SquareDetection.truncate_h6_square] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native algebra certificate {decl}: {ax}"

#print axioms csv_relation_isWeightedHomogeneous
#print axioms NaturalityWords200.entry_native_evaluate
#print axioms SquareDetection.native_h6_square_ne_zero
end KIP126.Checks.LinNativeWords200
