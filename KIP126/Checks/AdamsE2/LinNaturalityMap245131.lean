module

public import KIP126.LinProgram.Certificates.Naturality.Row245131Map
public import Lean.Elab.Command

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Kernel and trust-boundary checks for the two real native map certificates.
Mutations exercise the parser, recorded generator-image binding, degrees and
polynomial equality. Source row provenance remains the exporter's obligation;
actual-map comparison and full quotient descent are not asserted here. -/
namespace KIP126.Checks.LinNaturalityMap245131
open KIP126.LinModule.NaturalityMapCertificate
open KIP126.LinModule.RawData.Naturality245131

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local cbv_eval] KIP126.LinModule.NativeMapCertificates.cetaCode_get
  KIP126.LinE2.generatorDegree_eq_row
  KIP126.LinE2.SquareDetection.splitOn_comma
  KIP126.LinE2.SquareDetection.splitOn_semicolon
  KIP126.LinE2.SquareDetection.toNat?_eq_chars

example : check { sourceCertificate with generatorId := 0 } = false := by cbv
example : check { sourceCertificate with imageCode := "7,1" } = false := by cbv
example : check { sourceCertificate with
    source := { sourceCertificate.source with code := "8,1,1" } } = false := by cbv
example : check { sourceCertificate with
    target := { sourceCertificate.target with code := "0,1,8,1" } } = false := by cbv
example : check { sourceCertificate with
    target := { sourceCertificate.target with code := "unknown,1,7,1" } } = false := by cbv
example : check { sourceCertificate with
    source := { sourceCertificate.source with t := 20 } } = false := by cbv
example : check { sourceCertificate with
    target := { sourceCertificate.target with t := 18 } } = false := by cbv
example : check { targetCertificate with
    target := { targetCertificate.target with code := "2914,1,8,1" } } = false := by cbv
example : check { targetCertificate with
    target := { targetCertificate.target with code := "0,1,8" } } = false := by cbv

example : check { sourceCertificate with
    target := { sourceCertificate.target with code := "" } } = false := by cbv
example : check { sourceCertificate with
    target := { sourceCertificate.target with code := "0,1,7,1;" } } = false := by cbv

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "native map certificate imports actual-model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinModule.NaturalityMapCertificate.check_sound,
      ``KIP126.LinModule.NaturalityMapCertificate.check_sound_desc,
      ``KIP126.LinModule.Naturality245131.source_check,
      ``KIP126.LinModule.Naturality245131.target_check,
      ``KIP126.LinModule.Naturality245131.generator_one_image,
      ``KIP126.LinModule.Naturality245131.source_evaluate,
      ``KIP126.LinModule.Naturality245131.target_evaluate,
      ``KIP126.LinModule.Naturality245131.source_sphere_row_mem,
      ``KIP126.LinModule.Naturality245131.target_sphere_row_mem,
      ``KIP126.LinModule.Naturality245131.source_desc,
      ``KIP126.LinModule.Naturality245131.target_desc] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native map certificate {decl}: {ax}"

#print axioms KIP126.LinModule.Naturality245131.source_evaluate
#print axioms KIP126.LinModule.Naturality245131.target_evaluate
#print axioms KIP126.LinModule.Naturality245131.source_desc
#print axioms KIP126.LinModule.Naturality245131.target_desc
end KIP126.Checks.LinNaturalityMap245131
