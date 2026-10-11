module

public import KIP126.LinProgram.Certificates.Naturality.Words200.All
public import Lean.Elab.Command

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Full-batch scope and kernel trust audit. Native row IDs exhaust the fixed
selected interval; they are provenance labels, not mathematical basis claims.
The full Ceta relation premise remains explicit in `entry_desc`. -/
namespace KIP126.Checks.LinNaturalityWords200
open KIP126.LinModule BatchMapCertificate
open RawData.NaturalityWords200.Shard000

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
attribute [local cbv_eval] NativeMapCertificates.cetaCode_get
  KIP126.LinE2.generatorDegree_eq_row
  KIP126.LinE2.SquareDetection.splitOn_comma
  KIP126.LinE2.SquareDetection.splitOn_semicolon
  KIP126.LinE2.SquareDetection.toNat?_eq_chars

private def relationSample : Entry where
  source := ⟨43, 3, 14, 0, "2,2,2"⟩
  targetS := 3
  targetT := 12
  targets := [⟨25, 3, 12, 0, "1,2,3,1"⟩]
  witness := [⟨0, [[]]⟩]

example : check relationCodes relationSample = true := by cbv
example : check relationCodes { relationSample with witness := [] } = false := by cbv
example : check relationCodes { relationSample with witness := [⟨1, [[]]⟩] } = false := by cbv
example : check relationCodes { relationSample with targetT := 11 } = false := by cbv
example : check relationCodes { relationSample with targets := [] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, "2914,1"⟩] } = false := by cbv

example : NaturalityWords200.entries.length = 15951 := NaturalityWords200.entry_count
example : NaturalityWords200.entries.map (fun e => e.source.id) = List.range' 2 15951 :=
  NaturalityWords200.source_ids

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "native word certificate imports actual-model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``NaturalityWords200.selected_mem_joinRows,
      ``NaturalityWords200.relation_member, ``NaturalityWords200.basis_member,
      ``NaturalityWords200.CertifiedBatch.entry_evaluate,
      ``NaturalityWords200.CertifiedBatch.entry_desc,
      ``NaturalityWords200.entry_evaluate, ``NaturalityWords200.zero_evaluate,
      ``NaturalityWords200.entry_desc, ``NaturalityWords200.target_row_mem,
      ``NaturalityWords200.entry_count, ``NaturalityWords200.source_ids] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native word certificate {decl}: {ax}"

#print axioms NaturalityWords200.entry_evaluate
#print axioms NaturalityWords200.entry_desc
#print axioms NaturalityWords200.target_row_mem
#print axioms NaturalityWords200.source_ids
end KIP126.Checks.LinNaturalityWords200
