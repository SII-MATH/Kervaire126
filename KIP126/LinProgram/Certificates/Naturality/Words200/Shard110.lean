module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard110
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk043
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk045
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk046
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk048
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard110
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard110
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
  exact ⟨Shared.RelationChunk000.relation2_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk001.relation153_zero, Shared.RelationChunk001.relation168_zero, Shared.RelationChunk001.relation169_zero, Shared.RelationChunk002.relation244_zero, Shared.RelationChunk005.relation343_zero, Shared.RelationChunk006.relation363_zero, Shared.RelationChunk006.relation364_zero, Shared.RelationChunk007.relation410_zero, Shared.RelationChunk007.relation441_zero, Shared.RelationChunk011.relation599_zero, Shared.RelationChunk011.relation600_zero, Shared.RelationChunk011.relation601_zero, Shared.RelationChunk011.relation602_zero, Shared.RelationChunk014.relation709_zero, Shared.RelationChunk017.relation813_zero, Shared.RelationChunk017.relation814_zero, Shared.RelationChunk017.relation815_zero, Shared.RelationChunk017.relation816_zero, Shared.RelationChunk017.relation817_zero, Shared.RelationChunk017.relation854_zero, Shared.RelationChunk021.relation956_zero, Shared.RelationChunk024.relation1037_zero, Shared.RelationChunk024.relation1042_zero, Shared.RelationChunk029.relation1258_zero, Shared.RelationChunk029.relation1263_zero, Shared.RelationChunk043.relation1660_zero, Shared.RelationChunk045.relation1693_zero, Shared.RelationChunk046.relation1694_zero, Shared.RelationChunk046.relation1695_zero, Shared.RelationChunk046.relation1696_zero, Shared.RelationChunk046.relation1697_zero, Shared.RelationChunk046.relation1698_zero, Shared.RelationChunk046.relation1699_zero, Shared.RelationChunk048.relation1754_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14082 128 := by cbv
private def targetRows : List BasisRow := [⟨29, 191, 0, "8,1,13,2,292,1"⟩,
  ⟨29, 191, 1, "8,3,17,1,209,1"⟩,
  ⟨29, 191, 2, "0,2,64,1,301,1"⟩,
  ⟨29, 191, 3, "0,3,974,1"⟩,
  ⟨28, 191, 0, "13,1,23,1,346,1"⟩,
  ⟨28, 191, 2, "8,4,261,1"⟩,
  ⟨28, 191, 4, "0,3,977,1"⟩,
  ⟨28, 191, 5, "0,3,976,1"⟩,
  ⟨27, 191, 0, "17,1,655,1"⟩,
  ⟨27, 191, 1, "8,3,423,1"⟩,
  ⟨27, 191, 2, "2,1,963,1"⟩,
  ⟨27, 191, 3, "0,3,978,1"⟩,
  ⟨26, 191, 0, "1035,1"⟩,
  ⟨26, 191, 1, "64,1,318,1"⟩,
  ⟨26, 191, 2, "8,2,13,2,209,1"⟩,
  ⟨25, 191, 0, "72,1,293,1"⟩,
  ⟨25, 191, 1, "8,1,13,2,294,1"⟩,
  ⟨25, 191, 2, "1,1,998,1"⟩,
  ⟨24, 191, 0, "13,3,261,1"⟩,
  ⟨24, 191, 1, "8,1,72,1,209,1"⟩,
  ⟨24, 191, 2, "1,1,64,1,308,1"⟩,
  ⟨23, 191, 0, "13,3,262,1"⟩,
  ⟨23, 191, 1, "8,1,798,1"⟩,
  ⟨22, 191, 0, "1036,1"⟩,
  ⟨22, 191, 1, "9,1,761,1"⟩,
  ⟨21, 191, 1, "1,2,964,1"⟩,
  ⟨20, 191, 0, "1038,1"⟩,
  ⟨20, 191, 1, "0,1,1011,1"⟩,
  ⟨20, 191, 2, "0,4,965,1"⟩,
  ⟨19, 191, 0, "1041,1"⟩,
  ⟨19, 191, 1, "1040,1"⟩,
  ⟨19, 191, 2, "1039,1"⟩,
  ⟨19, 191, 3, "0,1,1014,1"⟩,
  ⟨19, 191, 4, "0,3,987,1"⟩,
  ⟨18, 191, 0, "1044,1"⟩,
  ⟨18, 191, 3, "0,1,1016,1"⟩,
  ⟨18, 191, 4, "0,1,1015,1"⟩,
  ⟨18, 191, 5, "0,3,17,2,324,1"⟩,
  ⟨17, 191, 0, "1045,1"⟩,
  ⟨17, 191, 1, "8,1,39,1,324,1"⟩,
  ⟨17, 191, 2, "1,1,1004,1"⟩,
  ⟨17, 191, 3, "1,1,122,1,209,1"⟩,
  ⟨17, 191, 4, "0,1,1018,1"⟩,
  ⟨17, 191, 5, "0,1,1017,1"⟩,
  ⟨17, 191, 6, "0,2,1005,1"⟩,
  ⟨17, 191, 7, "0,3,59,1,324,1"⟩,
  ⟨16, 191, 1, "8,1,40,1,324,1"⟩,
  ⟨16, 191, 2, "2,1,967,1"⟩,
  ⟨16, 191, 3, "0,1,1021,1"⟩,
  ⟨16, 191, 4, "0,1,1020,1"⟩,
  ⟨15, 191, 0, "17,1,20,1,324,1"⟩,
  ⟨15, 191, 1, "13,1,734,1"⟩,
  ⟨15, 191, 2, "0,1,1024,1"⟩,
  ⟨14, 191, 1, "63,1,324,1"⟩,
  ⟨13, 191, 0, "8,1,9,1,13,1,324,1"⟩,
  ⟨12, 191, 0, "9,1,32,1,324,1"⟩,
  ⟨12, 191, 1, "0,1,1027,1"⟩,
  ⟨11, 191, 1, "0,1,1028,1"⟩,
  ⟨10, 191, 0, "0,1,17,1,18,1,324,1"⟩,
  ⟨192, 192, 0, "0,192"⟩,
  ⟨63, 192, 0, "0,3,995,1"⟩,
  ⟨59, 192, 0, "8,1,804,1"⟩,
  ⟨56, 192, 0, "8,3,431,1"⟩,
  ⟨55, 192, 0, "8,2,16,1,296,1"⟩,
  ⟨54, 192, 0, "8,2,17,1,296,1"⟩,
  ⟨53, 192, 0, "8,2,607,1"⟩,
  ⟨52, 192, 0, "8,5,182,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8379_mem, Shared.BasisChunk008.row8380_mem, Shared.BasisChunk008.row8381_mem, Shared.BasisChunk008.row8382_mem, Shared.BasisChunk008.row8383_mem, Shared.BasisChunk008.row8385_mem, Shared.BasisChunk008.row8387_mem, Shared.BasisChunk008.row8388_mem, Shared.BasisChunk008.row8389_mem, Shared.BasisChunk008.row8390_mem, Shared.BasisChunk008.row8391_mem, Shared.BasisChunk008.row8392_mem, Shared.BasisChunk008.row8393_mem, Shared.BasisChunk008.row8394_mem, Shared.BasisChunk008.row8395_mem, Shared.BasisChunk008.row8396_mem, Shared.BasisChunk008.row8397_mem, Shared.BasisChunk008.row8398_mem, Shared.BasisChunk008.row8399_mem, Shared.BasisChunk008.row8400_mem, Shared.BasisChunk008.row8401_mem, Shared.BasisChunk008.row8402_mem, Shared.BasisChunk008.row8403_mem, Shared.BasisChunk008.row8404_mem, Shared.BasisChunk008.row8405_mem, Shared.BasisChunk008.row8407_mem, Shared.BasisChunk008.row8408_mem, Shared.BasisChunk008.row8409_mem, Shared.BasisChunk008.row8410_mem, Shared.BasisChunk008.row8411_mem, Shared.BasisChunk008.row8412_mem, Shared.BasisChunk008.row8413_mem, Shared.BasisChunk008.row8414_mem, Shared.BasisChunk008.row8415_mem, Shared.BasisChunk008.row8416_mem, Shared.BasisChunk008.row8419_mem, Shared.BasisChunk008.row8420_mem, Shared.BasisChunk008.row8421_mem, Shared.BasisChunk008.row8422_mem, Shared.BasisChunk008.row8423_mem, Shared.BasisChunk008.row8424_mem, Shared.BasisChunk008.row8425_mem, Shared.BasisChunk008.row8426_mem, Shared.BasisChunk008.row8427_mem, Shared.BasisChunk008.row8428_mem, Shared.BasisChunk008.row8429_mem, Shared.BasisChunk008.row8431_mem, Shared.BasisChunk008.row8432_mem, Shared.BasisChunk008.row8433_mem, Shared.BasisChunk008.row8434_mem, Shared.BasisChunk008.row8435_mem, Shared.BasisChunk008.row8436_mem, Shared.BasisChunk008.row8437_mem, Shared.BasisChunk008.row8439_mem, Shared.BasisChunk008.row8440_mem, Shared.BasisChunk008.row8441_mem, Shared.BasisChunk008.row8442_mem, Shared.BasisChunk008.row8444_mem, Shared.BasisChunk008.row8445_mem, Shared.BasisChunk008.row8446_mem, Shared.BasisChunk008.row8447_mem, Shared.BasisChunk008.row8449_mem, Shared.BasisChunk008.row8451_mem, Shared.BasisChunk008.row8452_mem, Shared.BasisChunk008.row8453_mem, Shared.BasisChunk008.row8454_mem, Shared.BasisChunk008.row8455_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard110
