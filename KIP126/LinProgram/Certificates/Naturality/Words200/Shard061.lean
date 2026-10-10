import KIP126.LinProgram.Generated.Naturality.Words200.Shard061
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard061
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard061
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation100_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation181_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation184_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk006.relation367_zero, Shared.RelationChunk006.relation368_zero, Shared.RelationChunk006.relation369_zero, Shared.RelationChunk006.relation370_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation372_zero, Shared.RelationChunk006.relation377_zero, Shared.RelationChunk006.relation378_zero, Shared.RelationChunk006.relation379_zero, Shared.RelationChunk006.relation380_zero, Shared.RelationChunk007.relation426_zero, Shared.RelationChunk009.relation494_zero, Shared.RelationChunk009.relation495_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk011.relation585_zero, Shared.RelationChunk011.relation586_zero, Shared.RelationChunk011.relation587_zero, Shared.RelationChunk018.relation862_zero, Shared.RelationChunk018.relation863_zero, Shared.RelationChunk018.relation864_zero, Shared.RelationChunk018.relation866_zero, Shared.RelationChunk018.relation867_zero, Shared.RelationChunk018.relation874_zero, Shared.RelationChunk019.relation899_zero, Shared.RelationChunk019.relation904_zero, Shared.RelationChunk019.relation905_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7810 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 158, 0, "9,1,423,1"⟩,
  ⟨19, 158, 1, "0,1,8,1,449,1"⟩,
  ⟨19, 158, 2, "0,2,612,1"⟩,
  ⟨19, 158, 3, "0,8,562,1"⟩,
  ⟨18, 158, 1, "0,2,613,1"⟩,
  ⟨18, 158, 2, "0,6,575,1"⟩,
  ⟨17, 158, 0, "0,1,17,1,314,1"⟩,
  ⟨16, 158, 1, "0,2,3,1,540,1"⟩,
  ⟨15, 158, 0, "630,1"⟩,
  ⟨15, 158, 1, "1,1,3,1,540,1"⟩,
  ⟨15, 158, 2, "0,2,8,1,443,1"⟩,
  ⟨14, 158, 0, "0,1,13,1,373,1"⟩,
  ⟨14, 158, 1, "0,2,8,1,445,1"⟩,
  ⟨14, 158, 2, "0,2,3,1,543,1"⟩,
  ⟨13, 158, 0, "2,1,590,1"⟩,
  ⟨13, 158, 1, "0,2,615,1"⟩,
  ⟨13, 158, 2, "0,2,3,1,544,1"⟩,
  ⟨12, 158, 1, "7,1,485,1"⟩,
  ⟨12, 158, 2, "0,2,15,1,324,1"⟩,
  ⟨9, 158, 1, "17,1,69,2"⟩,
  ⟨9, 158, 3, "0,2,617,1"⟩,
  ⟨8, 158, 0, "17,1,324,1"⟩,
  ⟨8, 158, 1, "1,1,617,1"⟩,
  ⟨159, 159, 0, "0,159"⟩,
  ⟨49, 159, 0, "0,3,17,1,296,1"⟩,
  ⟨48, 159, 1, "0,3,606,1"⟩,
  ⟨47, 159, 0, "8,1,470,1"⟩,
  ⟨46, 159, 0, "17,1,326,1"⟩,
  ⟨45, 159, 0, "634,1"⟩,
  ⟨44, 159, 0, "8,3,199,1"⟩,
  ⟨43, 159, 0, "8,3,200,1"⟩,
  ⟨42, 159, 1, "8,2,17,1,153,1"⟩,
  ⟨41, 159, 0, "636,1"⟩,
  ⟨41, 159, 1, "8,2,283,1"⟩,
  ⟨40, 159, 0, "8,5,77,1"⟩,
  ⟨39, 159, 0, "8,5,78,1"⟩,
  ⟨38, 159, 1, "8,4,17,1,56,1"⟩,
  ⟨37, 159, 0, "8,1,16,1,225,1"⟩,
  ⟨37, 159, 1, "8,4,136,1"⟩,
  ⟨37, 159, 2, "0,1,8,1,452,1"⟩,
  ⟨36, 159, 0, "8,1,17,1,225,1"⟩,
  ⟨36, 159, 1, "8,7,19,1"⟩,
  ⟨35, 159, 1, "8,7,20,1"⟩,
  ⟨34, 159, 0, "8,4,137,1"⟩,
  ⟨34, 159, 1, "8,6,45,1"⟩,
  ⟨33, 159, 0, "8,4,138,1"⟩,
  ⟨33, 159, 1, "8,6,46,1"⟩,
  ⟨33, 159, 2, "0,15,500,1"⟩,
  ⟨32, 159, 0, "8,2,16,1,154,1"⟩,
  ⟨32, 159, 1, "8,5,9,1,13,2"⟩,
  ⟨32, 159, 3, "0,31,324,1"⟩,
  ⟨31, 159, 0, "8,2,17,1,154,1"⟩,
  ⟨31, 159, 1, "8,4,9,1,13,1,32,1"⟩,
  ⟨31, 159, 2, "0,1,623,1"⟩,
  ⟨30, 159, 1, "8,3,9,1,13,2,23,1"⟩,
  ⟨30, 159, 2, "8,5,79,1"⟩,
  ⟨30, 159, 3, "0,4,64,1,149,1"⟩,
  ⟨29, 159, 0, "8,2,9,1,13,2,51,1"⟩,
  ⟨29, 159, 1, "8,5,80,1"⟩,
  ⟨29, 159, 2, "0,4,598,1"⟩,
  ⟨28, 159, 1, "8,1,9,1,13,5"⟩,
  ⟨28, 159, 2, "8,3,22,1,80,1"⟩,
  ⟨28, 159, 4, "0,4,17,1,292,1"⟩,
  ⟨27, 159, 0, "9,1,13,4,32,1"⟩,
  ⟨27, 159, 1, "8,1,64,1,113,1"⟩,
  ⟨27, 159, 2, "8,3,23,1,80,1"⟩,
  ⟨27, 159, 3, "0,1,8,2,278,1"⟩,
  ⟨27, 159, 4, "0,4,601,1"⟩,
  ⟨27, 159, 5, "0,4,600,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4708_mem, Shared.BasisChunk004.row4709_mem, Shared.BasisChunk004.row4710_mem, Shared.BasisChunk004.row4711_mem, Shared.BasisChunk004.row4713_mem, Shared.BasisChunk004.row4714_mem, Shared.BasisChunk004.row4715_mem, Shared.BasisChunk004.row4717_mem, Shared.BasisChunk004.row4718_mem, Shared.BasisChunk004.row4719_mem, Shared.BasisChunk004.row4720_mem, Shared.BasisChunk004.row4721_mem, Shared.BasisChunk004.row4722_mem, Shared.BasisChunk004.row4723_mem, Shared.BasisChunk004.row4724_mem, Shared.BasisChunk004.row4725_mem, Shared.BasisChunk004.row4726_mem, Shared.BasisChunk004.row4728_mem, Shared.BasisChunk004.row4729_mem, Shared.BasisChunk004.row4734_mem, Shared.BasisChunk004.row4736_mem, Shared.BasisChunk004.row4737_mem, Shared.BasisChunk004.row4738_mem, Shared.BasisChunk004.row4739_mem, Shared.BasisChunk004.row4740_mem, Shared.BasisChunk004.row4742_mem, Shared.BasisChunk004.row4743_mem, Shared.BasisChunk004.row4744_mem, Shared.BasisChunk004.row4745_mem, Shared.BasisChunk004.row4746_mem, Shared.BasisChunk004.row4747_mem, Shared.BasisChunk004.row4749_mem, Shared.BasisChunk004.row4750_mem, Shared.BasisChunk004.row4751_mem, Shared.BasisChunk004.row4752_mem, Shared.BasisChunk004.row4753_mem, Shared.BasisChunk004.row4755_mem, Shared.BasisChunk004.row4756_mem, Shared.BasisChunk004.row4757_mem, Shared.BasisChunk004.row4758_mem, Shared.BasisChunk004.row4759_mem, Shared.BasisChunk004.row4760_mem, Shared.BasisChunk004.row4762_mem, Shared.BasisChunk004.row4763_mem, Shared.BasisChunk004.row4764_mem, Shared.BasisChunk004.row4765_mem, Shared.BasisChunk004.row4766_mem, Shared.BasisChunk004.row4767_mem, Shared.BasisChunk004.row4768_mem, Shared.BasisChunk004.row4769_mem, Shared.BasisChunk004.row4771_mem, Shared.BasisChunk004.row4772_mem, Shared.BasisChunk004.row4773_mem, Shared.BasisChunk004.row4774_mem, Shared.BasisChunk004.row4776_mem, Shared.BasisChunk004.row4777_mem, Shared.BasisChunk004.row4778_mem, Shared.BasisChunk004.row4779_mem, Shared.BasisChunk004.row4780_mem, Shared.BasisChunk004.row4781_mem, Shared.BasisChunk004.row4783_mem, Shared.BasisChunk004.row4784_mem, Shared.BasisChunk004.row4786_mem, Shared.BasisChunk004.row4787_mem, Shared.BasisChunk004.row4788_mem, Shared.BasisChunk004.row4789_mem, Shared.BasisChunk004.row4790_mem, Shared.BasisChunk004.row4791_mem, Shared.BasisChunk004.row4792_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard061
