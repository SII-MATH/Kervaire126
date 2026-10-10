import KIP126.LinProgram.Generated.Naturality.Words200.Shard085
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard085
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard085
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
  exact ⟨Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation31_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk010.relation542_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation552_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk010.relation555_zero, Shared.RelationChunk010.relation556_zero, Shared.RelationChunk010.relation557_zero, Shared.RelationChunk010.relation558_zero, Shared.RelationChunk010.relation559_zero, Shared.RelationChunk010.relation560_zero, Shared.RelationChunk010.relation561_zero, Shared.RelationChunk012.relation627_zero, Shared.RelationChunk013.relation672_zero, Shared.RelationChunk013.relation675_zero, Shared.RelationChunk015.relation780_zero, Shared.RelationChunk015.relation781_zero, Shared.RelationChunk018.relation872_zero, Shared.RelationChunk018.relation877_zero, Shared.RelationChunk018.relation879_zero, Shared.RelationChunk029.relation1248_zero, Shared.RelationChunk030.relation1265_zero, Shared.RelationChunk030.relation1266_zero, Shared.RelationChunk030.relation1267_zero, Shared.RelationChunk030.relation1268_zero, Shared.RelationChunk030.relation1269_zero, Shared.RelationChunk031.relation1310_zero, Shared.RelationChunk031.relation1311_zero, Shared.RelationChunk031.relation1312_zero, Shared.RelationChunk031.relation1313_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10882 128 := by cbv
private def targetRows : List BasisRow := [⟨18, 175, 1, "75,1,212,1"⟩,
  ⟨18, 175, 2, "0,1,2,1,763,1"⟩,
  ⟨18, 175, 3, "0,7,743,1"⟩,
  ⟨17, 175, 0, "76,1,212,1"⟩,
  ⟨17, 175, 2, "0,15,18,1,324,1"⟩,
  ⟨16, 175, 0, "107,1,174,1"⟩,
  ⟨16, 175, 2, "13,1,569,1"⟩,
  ⟨16, 175, 3, "0,2,18,1,475,1"⟩,
  ⟨15, 175, 1, "824,1"⟩,
  ⟨15, 175, 2, "75,1,213,1"⟩,
  ⟨15, 175, 3, "13,1,570,1"⟩,
  ⟨15, 175, 4, "0,1,814,1"⟩,
  ⟨15, 175, 5, "0,2,801,1"⟩,
  ⟨15, 175, 6, "0,2,39,1,324,1"⟩,
  ⟨14, 175, 0, "76,1,213,1"⟩,
  ⟨14, 175, 1, "3,1,731,1"⟩,
  ⟨14, 175, 2, "3,1,730,1"⟩,
  ⟨14, 175, 3, "2,2,732,1"⟩,
  ⟨14, 175, 4, "0,1,815,1"⟩,
  ⟨14, 175, 5, "0,2,40,1,324,1"⟩,
  ⟨13, 175, 1, "2,2,734,1"⟩,
  ⟨13, 175, 2, "0,1,817,1"⟩,
  ⟨13, 175, 3, "0,1,3,1,719,1"⟩,
  ⟨13, 175, 4, "0,3,793,1"⟩,
  ⟨12, 175, 1, "3,1,735,1"⟩,
  ⟨12, 175, 2, "3,1,734,1"⟩,
  ⟨12, 175, 3, "0,5,18,1,446,1"⟩,
  ⟨11, 175, 0, "827,1"⟩,
  ⟨11, 175, 1, "0,1,818,1"⟩,
  ⟨11, 175, 2, "0,2,802,1"⟩,
  ⟨11, 175, 3, "0,5,34,1,324,1"⟩,
  ⟨10, 175, 0, "828,1"⟩,
  ⟨10, 175, 2, "0,3,36,1,324,1"⟩,
  ⟨176, 176, 0, "0,176"⟩,
  ⟨58, 176, 0, "0,2,803,1"⟩,
  ⟨57, 176, 1, "0,2,804,1"⟩,
  ⟨54, 176, 0, "0,2,8,2,431,1"⟩,
  ⟨53, 176, 0, "0,2,8,1,16,1,296,1"⟩,
  ⟨50, 176, 0, "0,12,686,1"⟩,
  ⟨49, 176, 0, "0,48,324,1"⟩,
  ⟨48, 176, 0, "0,2,805,1"⟩,
  ⟨47, 176, 0, "0,2,806,1"⟩,
  ⟨44, 176, 0, "0,5,17,2,225,1"⟩,
  ⟨43, 176, 0, "0,2,8,2,433,1"⟩,
  ⟨40, 176, 0, "8,2,452,1"⟩,
  ⟨39, 176, 0, "16,1,17,1,244,1"⟩,
  ⟨38, 176, 0, "8,1,31,1,245,1"⟩,
  ⟨38, 176, 1, "0,2,64,1,224,1"⟩,
  ⟨37, 176, 0, "8,2,453,1"⟩,
  ⟨37, 176, 2, "0,2,64,1,225,1"⟩,
  ⟨36, 176, 0, "8,3,16,1,149,1"⟩,
  ⟨36, 176, 1, "0,3,17,1,491,1"⟩,
  ⟨35, 176, 0, "8,3,17,1,149,1"⟩,
  ⟨35, 176, 1, "0,2,809,1"⟩,
  ⟨35, 176, 2, "0,2,807,1"⟩,
  ⟨34, 176, 1, "8,3,277,1"⟩,
  ⟨34, 176, 3, "0,3,795,1"⟩,
  ⟨33, 176, 0, "17,1,516,1"⟩,
  ⟨33, 176, 1, "8,4,193,1"⟩,
  ⟨32, 176, 0, "830,1"⟩,
  ⟨32, 176, 1, "8,4,194,1"⟩,
  ⟨31, 176, 0, "831,1"⟩,
  ⟨31, 176, 1, "8,3,13,1,167,1"⟩,
  ⟨30, 176, 0, "8,1,64,1,160,1"⟩,
  ⟨30, 176, 1, "8,2,13,1,248,1"⟩,
  ⟨30, 176, 2, "8,3,278,1"⟩,
  ⟨30, 176, 3, "1,1,5,1,642,1"⟩,
  ⟨29, 176, 0, "8,1,624,1"⟩,
  ⟨29, 176, 1, "8,1,13,2,219,1"⟩,
  ⟨29, 176, 2, "8,2,454,1"⟩,
  ⟨28, 176, 0, "13,3,194,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6489_mem, Shared.BasisChunk006.row6490_mem, Shared.BasisChunk006.row6491_mem, Shared.BasisChunk006.row6492_mem, Shared.BasisChunk006.row6494_mem, Shared.BasisChunk006.row6495_mem, Shared.BasisChunk006.row6497_mem, Shared.BasisChunk006.row6498_mem, Shared.BasisChunk006.row6500_mem, Shared.BasisChunk006.row6501_mem, Shared.BasisChunk006.row6502_mem, Shared.BasisChunk006.row6503_mem, Shared.BasisChunk006.row6504_mem, Shared.BasisChunk006.row6505_mem, Shared.BasisChunk006.row6506_mem, Shared.BasisChunk006.row6507_mem, Shared.BasisChunk006.row6508_mem, Shared.BasisChunk006.row6509_mem, Shared.BasisChunk006.row6510_mem, Shared.BasisChunk006.row6511_mem, Shared.BasisChunk006.row6513_mem, Shared.BasisChunk006.row6514_mem, Shared.BasisChunk006.row6515_mem, Shared.BasisChunk006.row6516_mem, Shared.BasisChunk006.row6518_mem, Shared.BasisChunk006.row6519_mem, Shared.BasisChunk006.row6520_mem, Shared.BasisChunk006.row6521_mem, Shared.BasisChunk006.row6522_mem, Shared.BasisChunk006.row6523_mem, Shared.BasisChunk006.row6524_mem, Shared.BasisChunk006.row6525_mem, Shared.BasisChunk006.row6527_mem, Shared.BasisChunk006.row6528_mem, Shared.BasisChunk006.row6529_mem, Shared.BasisChunk006.row6531_mem, Shared.BasisChunk006.row6532_mem, Shared.BasisChunk006.row6533_mem, Shared.BasisChunk006.row6534_mem, Shared.BasisChunk006.row6535_mem, Shared.BasisChunk006.row6536_mem, Shared.BasisChunk006.row6537_mem, Shared.BasisChunk006.row6538_mem, Shared.BasisChunk006.row6539_mem, Shared.BasisChunk006.row6541_mem, Shared.BasisChunk006.row6542_mem, Shared.BasisChunk006.row6543_mem, Shared.BasisChunk006.row6544_mem, Shared.BasisChunk006.row6545_mem, Shared.BasisChunk006.row6547_mem, Shared.BasisChunk006.row6548_mem, Shared.BasisChunk006.row6549_mem, Shared.BasisChunk006.row6550_mem, Shared.BasisChunk006.row6551_mem, Shared.BasisChunk006.row6552_mem, Shared.BasisChunk006.row6554_mem, Shared.BasisChunk006.row6556_mem, Shared.BasisChunk006.row6557_mem, Shared.BasisChunk006.row6558_mem, Shared.BasisChunk006.row6559_mem, Shared.BasisChunk006.row6560_mem, Shared.BasisChunk006.row6561_mem, Shared.BasisChunk006.row6562_mem, Shared.BasisChunk006.row6563_mem, Shared.BasisChunk006.row6564_mem, Shared.BasisChunk006.row6565_mem, Shared.BasisChunk006.row6566_mem, Shared.BasisChunk006.row6567_mem, Shared.BasisChunk006.row6568_mem, Shared.BasisChunk006.row6569_mem, Shared.BasisChunk006.row6570_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard085
