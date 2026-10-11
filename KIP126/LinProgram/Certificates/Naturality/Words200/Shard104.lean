module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard104
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk036
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk039
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk041
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk043
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard104
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard104
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation115_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk003.relation263_zero, Shared.RelationChunk005.relation340_zero, Shared.RelationChunk008.relation474_zero, Shared.RelationChunk008.relation475_zero, Shared.RelationChunk008.relation476_zero, Shared.RelationChunk008.relation477_zero, Shared.RelationChunk008.relation478_zero, Shared.RelationChunk008.relation479_zero, Shared.RelationChunk008.relation480_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk015.relation782_zero, Shared.RelationChunk015.relation783_zero, Shared.RelationChunk015.relation784_zero, Shared.RelationChunk015.relation785_zero, Shared.RelationChunk026.relation1120_zero, Shared.RelationChunk026.relation1122_zero, Shared.RelationChunk026.relation1123_zero, Shared.RelationChunk026.relation1126_zero, Shared.RelationChunk026.relation1127_zero, Shared.RelationChunk026.relation1128_zero, Shared.RelationChunk036.relation1458_zero, Shared.RelationChunk039.relation1540_zero, Shared.RelationChunk039.relation1541_zero, Shared.RelationChunk041.relation1608_zero, Shared.RelationChunk041.relation1610_zero, Shared.RelationChunk041.relation1611_zero, Shared.RelationChunk041.relation1612_zero, Shared.RelationChunk041.relation1613_zero, Shared.RelationChunk041.relation1614_zero, Shared.RelationChunk041.relation1615_zero, Shared.RelationChunk041.relation1616_zero, Shared.RelationChunk041.relation1617_zero, Shared.RelationChunk041.relation1618_zero, Shared.RelationChunk041.relation1619_zero, Shared.RelationChunk041.relation1620_zero, Shared.RelationChunk041.relation1621_zero, Shared.RelationChunk041.relation1622_zero, Shared.RelationChunk041.relation1623_zero, Shared.RelationChunk041.relation1625_zero, Shared.RelationChunk041.relation1626_zero, Shared.RelationChunk041.relation1627_zero, Shared.RelationChunk041.relation1628_zero, Shared.RelationChunk043.relation1640_zero, Shared.RelationChunk043.relation1641_zero, Shared.RelationChunk043.relation1642_zero, Shared.RelationChunk043.relation1643_zero, Shared.RelationChunk043.relation1644_zero, Shared.RelationChunk043.relation1645_zero, Shared.RelationChunk043.relation1646_zero, Shared.RelationChunk043.relation1647_zero, Shared.RelationChunk043.relation1648_zero, Shared.RelationChunk043.relation1649_zero, Shared.RelationChunk043.relation1650_zero, Shared.RelationChunk043.relation1651_zero, Shared.RelationChunk043.relation1652_zero, Shared.RelationChunk043.relation1653_zero, Shared.RelationChunk043.relation1654_zero, Shared.RelationChunk043.relation1655_zero, Shared.RelationChunk043.relation1656_zero, Shared.RelationChunk043.relation1657_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13314 128 := by cbv
private def targetRows : List BasisRow := [⟨24, 187, 0, "1,1,941,1"⟩,
  ⟨23, 187, 0, "3,1,876,1"⟩,
  ⟨23, 187, 1, "2,2,877,1"⟩,
  ⟨22, 187, 1, "0,2,943,1"⟩,
  ⟨22, 187, 2, "0,5,908,1"⟩,
  ⟨21, 187, 0, "67,1,286,1"⟩,
  ⟨21, 187, 2, "0,1,959,1"⟩,
  ⟨21, 187, 3, "0,5,50,1,324,1"⟩,
  ⟨20, 187, 0, "67,1,287,1"⟩,
  ⟨20, 187, 2, "13,1,677,1"⟩,
  ⟨20, 187, 3, "0,1,960,1"⟩,
  ⟨19, 187, 1, "13,1,679,1"⟩,
  ⟨19, 187, 2, "0,2,55,1,324,1"⟩,
  ⟨18, 187, 0, "13,2,450,1"⟩,
  ⟨18, 187, 1, "0,2,56,1,324,1"⟩,
  ⟨17, 187, 0, "13,1,682,1"⟩,
  ⟨17, 187, 1, "13,1,681,1"⟩,
  ⟨16, 187, 0, "966,1"⟩,
  ⟨16, 187, 1, "965,1"⟩,
  ⟨16, 187, 2, "68,1,288,1"⟩,
  ⟨15, 187, 0, "967,1"⟩,
  ⟨15, 187, 1, "3,1,882,1"⟩,
  ⟨15, 187, 2, "0,1,3,2,769,1"⟩,
  ⟨14, 187, 1, "0,1,2,1,912,1"⟩,
  ⟨13, 187, 0, "2,2,884,1"⟩,
  ⟨10, 187, 0, "1,1,13,1,660,1"⟩,
  ⟨9, 187, 0, "2,1,53,1,324,1"⟩,
  ⟨188, 188, 0, "0,188"⟩,
  ⟨62, 188, 0, "0,2,951,1"⟩,
  ⟨61, 188, 1, "0,60,324,1"⟩,
  ⟨58, 188, 0, "0,2,8,2,553,1"⟩,
  ⟨57, 188, 0, "0,2,8,2,554,1"⟩,
  ⟨55, 188, 0, "0,5,916,1"⟩,
  ⟨54, 188, 0, "0,5,917,1"⟩,
  ⟨52, 188, 0, "0,2,952,1"⟩,
  ⟨51, 188, 0, "0,2,953,1"⟩,
  ⟨47, 188, 0, "0,2,8,2,556,1"⟩,
  ⟨44, 188, 0, "8,1,16,1,452,1"⟩,
  ⟨43, 188, 0, "8,1,17,1,452,1"⟩,
  ⟨42, 188, 0, "8,1,49,1,245,1"⟩,
  ⟨41, 188, 0, "8,2,572,1"⟩,
  ⟨40, 188, 0, "8,4,244,1"⟩,
  ⟨39, 188, 0, "8,2,16,1,17,1,149,1"⟩,
  ⟨38, 188, 1, "8,4,245,1"⟩,
  ⟨37, 188, 0, "17,1,623,1"⟩,
  ⟨37, 188, 1, "8,4,247,1"⟩,
  ⟨36, 188, 1, "8,5,166,1"⟩,
  ⟨36, 188, 2, "0,4,149,2"⟩,
  ⟨35, 188, 0, "972,1"⟩,
  ⟨35, 188, 1, "8,5,167,1"⟩,
  ⟨35, 188, 2, "0,4,927,1"⟩,
  ⟨34, 188, 0, "8,1,64,1,206,1"⟩,
  ⟨34, 188, 1, "8,3,380,1"⟩,
  ⟨34, 188, 2, "8,4,248,1"⟩,
  ⟨34, 188, 4, "0,6,64,1,260,1"⟩,
  ⟨33, 188, 0, "8,1,113,1,149,1"⟩,
  ⟨33, 188, 1, "8,2,17,1,278,1"⟩,
  ⟨33, 188, 2, "8,3,13,1,219,1"⟩,
  ⟨33, 188, 3, "0,4,64,1,274,1"⟩,
  ⟨33, 188, 4, "0,6,897,1"⟩,
  ⟨32, 188, 0, "8,1,17,1,454,1"⟩,
  ⟨32, 188, 1, "8,2,573,1"⟩,
  ⟨32, 188, 2, "8,2,13,2,194,1"⟩,
  ⟨32, 188, 3, "0,5,921,1"⟩,
  ⟨32, 188, 4, "0,5,919,1"⟩,
  ⟨31, 188, 0, "8,1,42,1,278,1"⟩,
  ⟨31, 188, 1, "8,1,13,3,167,1"⟩,
  ⟨31, 188, 2, "8,2,574,1"⟩,
  ⟨31, 188, 3, "0,3,64,1,278,1"⟩,
  ⟨31, 188, 4, "0,6,898,1"⟩,
  ⟨30, 188, 0, "13,3,248,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7910_mem, Shared.BasisChunk007.row7911_mem, Shared.BasisChunk007.row7912_mem, Shared.BasisChunk007.row7914_mem, Shared.BasisChunk007.row7915_mem, Shared.BasisChunk007.row7916_mem, Shared.BasisChunk007.row7918_mem, Shared.BasisChunk007.row7919_mem, Shared.BasisChunk007.row7920_mem, Shared.BasisChunk007.row7922_mem, Shared.BasisChunk007.row7923_mem, Shared.BasisChunk007.row7925_mem, Shared.BasisChunk007.row7926_mem, Shared.BasisChunk007.row7927_mem, Shared.BasisChunk007.row7928_mem, Shared.BasisChunk007.row7929_mem, Shared.BasisChunk007.row7930_mem, Shared.BasisChunk007.row7931_mem, Shared.BasisChunk007.row7932_mem, Shared.BasisChunk007.row7933_mem, Shared.BasisChunk007.row7934_mem, Shared.BasisChunk007.row7935_mem, Shared.BasisChunk007.row7936_mem, Shared.BasisChunk007.row7938_mem, Shared.BasisChunk007.row7939_mem, Shared.BasisChunk007.row7942_mem, Shared.BasisChunk007.row7943_mem, Shared.BasisChunk007.row7946_mem, Shared.BasisChunk007.row7947_mem, Shared.BasisChunk007.row7949_mem, Shared.BasisChunk007.row7950_mem, Shared.BasisChunk007.row7951_mem, Shared.BasisChunk007.row7952_mem, Shared.BasisChunk007.row7953_mem, Shared.BasisChunk007.row7954_mem, Shared.BasisChunk007.row7955_mem, Shared.BasisChunk007.row7957_mem, Shared.BasisChunk007.row7959_mem, Shared.BasisChunk007.row7960_mem, Shared.BasisChunk007.row7961_mem, Shared.BasisChunk007.row7962_mem, Shared.BasisChunk007.row7964_mem, Shared.BasisChunk007.row7965_mem, Shared.BasisChunk007.row7967_mem, Shared.BasisChunk007.row7969_mem, Shared.BasisChunk007.row7970_mem, Shared.BasisChunk007.row7972_mem, Shared.BasisChunk007.row7973_mem, Shared.BasisChunk007.row7974_mem, Shared.BasisChunk007.row7975_mem, Shared.BasisChunk007.row7976_mem, Shared.BasisChunk007.row7977_mem, Shared.BasisChunk007.row7978_mem, Shared.BasisChunk007.row7979_mem, Shared.BasisChunk007.row7981_mem, Shared.BasisChunk007.row7982_mem, Shared.BasisChunk007.row7983_mem, Shared.BasisChunk007.row7984_mem, Shared.BasisChunk007.row7985_mem, Shared.BasisChunk007.row7986_mem, Shared.BasisChunk007.row7987_mem, Shared.BasisChunk007.row7988_mem, Shared.BasisChunk007.row7989_mem, Shared.BasisChunk007.row7990_mem, Shared.BasisChunk007.row7991_mem, Shared.BasisChunk007.row7992_mem, Shared.BasisChunk007.row7993_mem, Shared.BasisChunk007.row7994_mem, Shared.BasisChunk007.row7995_mem, Shared.BasisChunk007.row7996_mem, Shared.BasisChunk007.row7997_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard104
