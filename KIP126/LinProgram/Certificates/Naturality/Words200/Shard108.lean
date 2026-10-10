import KIP126.LinProgram.Generated.Naturality.Words200.Shard108
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk044
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk045
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard108
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard108
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
theorem relations_zero : ∀ code ∈ relationCodes, nativeImage code = 0 := by
  simp only [relationCodes, List.forall_mem_cons]
  exact ⟨Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk044.relation1690_zero, Shared.RelationChunk045.relation1691_zero, Shared.RelationChunk045.relation1692_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13826 128 := by cbv
private def targetRows : List BasisRow := [⟨42, 190, 0, "1,1,5,1,64,1,224,1"⟩,
  ⟨41, 190, 0, "0,1,64,1,297,1"⟩,
  ⟨40, 190, 0, "0,1,64,1,298,1"⟩,
  ⟨40, 190, 1, "0,2,8,1,759,1"⟩,
  ⟨39, 190, 0, "0,1,8,1,778,1"⟩,
  ⟨39, 190, 1, "0,2,17,1,623,1"⟩,
  ⟨38, 190, 0, "0,6,149,2"⟩,
  ⟨37, 190, 0, "0,6,927,1"⟩,
  ⟨36, 190, 0, "0,8,64,1,260,1"⟩,
  ⟨35, 190, 0, "0,6,64,1,274,1"⟩,
  ⟨35, 190, 1, "0,8,897,1"⟩,
  ⟨34, 190, 0, "0,7,919,1"⟩,
  ⟨33, 190, 1, "0,8,898,1"⟩,
  ⟨32, 190, 0, "16,1,642,1"⟩,
  ⟨31, 190, 0, "17,1,642,1"⟩,
  ⟨31, 190, 1, "0,1,64,3"⟩,
  ⟨30, 190, 0, "8,1,784,1"⟩,
  ⟨30, 190, 1, "0,1,64,1,299,1"⟩,
  ⟨30, 190, 2, "0,2,16,1,627,1"⟩,
  ⟨29, 190, 0, "13,1,715,1"⟩,
  ⟨29, 190, 1, "0,2,17,1,627,1"⟩,
  ⟨29, 190, 2, "0,3,963,1"⟩,
  ⟨28, 190, 0, "13,1,716,1"⟩,
  ⟨28, 190, 1, "13,5,83,1"⟩,
  ⟨28, 190, 2, "0,1,64,1,301,1"⟩,
  ⟨28, 190, 3, "0,2,974,1"⟩,
  ⟨28, 190, 4, "0,2,973,1"⟩,
  ⟨27, 190, 0, "1010,1"⟩,
  ⟨27, 190, 1, "9,1,13,4,95,1"⟩,
  ⟨27, 190, 2, "0,2,977,1"⟩,
  ⟨27, 190, 3, "0,2,976,1"⟩,
  ⟨26, 190, 0, "1,1,975,1"⟩,
  ⟨26, 190, 2, "0,2,978,1"⟩,
  ⟨26, 190, 3, "0,2,13,1,690,1"⟩,
  ⟨25, 190, 1, "0,1,8,1,17,1,475,1"⟩,
  ⟨25, 190, 2, "0,1,2,1,941,1"⟩,
  ⟨24, 190, 0, "1,1,979,1"⟩,
  ⟨23, 190, 0, "0,1,999,1"⟩,
  ⟨22, 190, 1, "13,1,23,1,335,1"⟩,
  ⟨22, 190, 2, "0,2,982,1"⟩,
  ⟨21, 190, 0, "9,1,75,1,188,1"⟩,
  ⟨21, 190, 1, "0,2,984,1"⟩,
  ⟨20, 190, 0, "75,1,286,1"⟩,
  ⟨20, 190, 1, "0,1,1000,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8233_mem, Shared.BasisChunk008.row8234_mem, Shared.BasisChunk008.row8235_mem, Shared.BasisChunk008.row8236_mem, Shared.BasisChunk008.row8237_mem, Shared.BasisChunk008.row8238_mem, Shared.BasisChunk008.row8239_mem, Shared.BasisChunk008.row8240_mem, Shared.BasisChunk008.row8241_mem, Shared.BasisChunk008.row8242_mem, Shared.BasisChunk008.row8243_mem, Shared.BasisChunk008.row8244_mem, Shared.BasisChunk008.row8246_mem, Shared.BasisChunk008.row8247_mem, Shared.BasisChunk008.row8248_mem, Shared.BasisChunk008.row8249_mem, Shared.BasisChunk008.row8250_mem, Shared.BasisChunk008.row8251_mem, Shared.BasisChunk008.row8252_mem, Shared.BasisChunk008.row8253_mem, Shared.BasisChunk008.row8254_mem, Shared.BasisChunk008.row8255_mem, Shared.BasisChunk008.row8256_mem, Shared.BasisChunk008.row8257_mem, Shared.BasisChunk008.row8258_mem, Shared.BasisChunk008.row8259_mem, Shared.BasisChunk008.row8260_mem, Shared.BasisChunk008.row8261_mem, Shared.BasisChunk008.row8262_mem, Shared.BasisChunk008.row8263_mem, Shared.BasisChunk008.row8264_mem, Shared.BasisChunk008.row8265_mem, Shared.BasisChunk008.row8267_mem, Shared.BasisChunk008.row8268_mem, Shared.BasisChunk008.row8270_mem, Shared.BasisChunk008.row8271_mem, Shared.BasisChunk008.row8272_mem, Shared.BasisChunk008.row8273_mem, Shared.BasisChunk008.row8275_mem, Shared.BasisChunk008.row8276_mem, Shared.BasisChunk008.row8277_mem, Shared.BasisChunk008.row8278_mem, Shared.BasisChunk008.row8279_mem, Shared.BasisChunk008.row8280_mem, by simp⟩
private def targetCheck (r : BasisRecord) : Bool :=
  targetRows.any (fun b => decide (b.s = r.s ∧ b.t = r.t ∧
    b.index = r.localIndex ∧ b.monomial = r.code))
private theorem targetCheck_sound (r : BasisRecord) (h : targetCheck r = true) :
    basisRow r ∈ basisRows := by
  obtain ⟨b, hb, h⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at h
  have he : b = basisRow r := by cases b; cases r; simp_all [basisRow]
  rw [← he]
  exact targetRows_mem b hb
private theorem targets_checked : entries.all (fun e => e.targets.all targetCheck) = true := by cbv
theorem targets_mem (e : Entry) (he : e ∈ entries) (r : BasisRecord) (hr : r ∈ e.targets) :
    basisRow r ∈ basisRows :=
  targetCheck_sound r ((List.all_eq_true.mp ((List.all_eq_true.mp targets_checked) e he)) r hr)
def certificate : CertifiedBatch :=
  ⟨relationCodes, entries, all_checks, relations_zero, targets_mem⟩
end KIP126.LinModule.NaturalityWords200.Shard108
