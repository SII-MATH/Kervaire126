module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationsFirst
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
theorem relation0_mem : "0,1,1,1" ∈ LinE2.RawData.relations := by
  exact List.mem_append_left _ (by simp [LinE2.RawData.firstRelations])
theorem relation0_zero : nativeImage "0,1,1,1" = 0 := by
  change projection (relationPolynomial "0,1,1,1") = 0
  exact csv_relation_zero _ relation0_mem
theorem relation1_mem : "1,1,2,1" ∈ LinE2.RawData.relations := by
  exact List.mem_append_left _ (by simp [LinE2.RawData.firstRelations])
theorem relation1_zero : nativeImage "1,1,2,1" = 0 := by
  change projection (relationPolynomial "1,1,2,1") = 0
  exact csv_relation_zero _ relation1_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationsFirst
