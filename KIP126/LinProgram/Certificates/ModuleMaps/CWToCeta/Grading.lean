module

public import KIP126.LinProgram.Certificates.ModuleMaps.ModuleGrading
public import KIP126.LinProgram.Certificates.ModuleMaps.CWToCeta.Data
public import KIP126.LinProgram.Model.Ceta.Grading
public import KIP126.LinProgram.Model.CWNuEta.Grading
public import KIP126.LinProgram.Certificates.SquareDimension.Generators.Proofs

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Every generator image in the complete native CW-to-Ceta graph has its
original bidegree shifted by (0,-4). The complete original source and target
quotients are retained. This degree proof does not supply either the source
relation certificates or comparison with an actual spectrum map. -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
namespace KIP126.LinModule.NativeMapCertificates
open KIP126.Core.Algebra
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates NamedElementCertificates
open KIP126.LinE2.NativeModuleCertificates.Support

theorem cwCode_get (i : Fin RawData.Maps.CWToCeta.sourceGeneratorCount) :
    RawData.Maps.CWToCeta.imageCode i =
      (RawData.Maps.CWToCeta.rows[i.val]'(by
        have h : RawData.Maps.CWToCeta.rows.size = RawData.Maps.CWToCeta.sourceGeneratorCount := rfl
        simpa only [h] using i.isLt)).image := by
  simp only [RawData.Maps.CWToCeta.imageCode, RawData.Maps.CWToCeta.imageCodes, Array.getElem_map]

attribute [local cbv_eval] cwCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.toNat?_eq_chars

def cwDegreeCheck (i : Nat) : Bool :=
  if h : i < RawData.CWNuEta.generatorCount then
    homogeneousModuleTermsCheck (CWToCeta.imageTerms ⟨i,h⟩) Ceta.generatorDegree
      (CWNuEta.generatorDegree ⟨i,h⟩ + (0,-4))
  else false

-- Keep each kernel computation small; the checked ranges still cover every original index.
private theorem all_range'_join (start left right : Nat) (p : Nat → Bool)
    (hl : (List.range' start left).all p = true)
    (hr : (List.range' (start + left) right).all p = true) :
    (List.range' start (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hl, hr]
  rfl

private theorem cw_degree_chunk_000 :
    ((List.range' 0 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_001 :
    ((List.range' 32 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_002 :
    ((List.range' 64 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_003 :
    ((List.range' 96 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_004 :
    ((List.range' 128 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_005 :
    ((List.range' 160 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_006 :
    ((List.range' 192 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_007 :
    ((List.range' 224 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_008 :
    ((List.range' 256 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_009 :
    ((List.range' 288 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_010 :
    ((List.range' 320 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_011 :
    ((List.range' 352 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_012 :
    ((List.range' 384 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_013 :
    ((List.range' 416 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_014 :
    ((List.range' 448 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_015 :
    ((List.range' 480 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_016 :
    ((List.range' 512 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_017 :
    ((List.range' 544 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_018 :
    ((List.range' 576 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_019 :
    ((List.range' 608 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_020 :
    ((List.range' 640 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_021 :
    ((List.range' 672 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_022 :
    ((List.range' 704 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_023 :
    ((List.range' 736 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_024 :
    ((List.range' 768 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_025 :
    ((List.range' 800 32).all cwDegreeCheck) = true := by cbv

private theorem cw_degree_chunk_026 :
    ((List.range' 832 12).all cwDegreeCheck) = true := by cbv

theorem cw_degree_all :
    ((List.range RawData.CWNuEta.generatorCount).all cwDegreeCheck) = true := by
  rw [List.range_eq_range']
  refine all_range'_join 0 32 812 cwDegreeCheck cw_degree_chunk_000 ?_
  refine all_range'_join 32 32 780 cwDegreeCheck cw_degree_chunk_001 ?_
  refine all_range'_join 64 32 748 cwDegreeCheck cw_degree_chunk_002 ?_
  refine all_range'_join 96 32 716 cwDegreeCheck cw_degree_chunk_003 ?_
  refine all_range'_join 128 32 684 cwDegreeCheck cw_degree_chunk_004 ?_
  refine all_range'_join 160 32 652 cwDegreeCheck cw_degree_chunk_005 ?_
  refine all_range'_join 192 32 620 cwDegreeCheck cw_degree_chunk_006 ?_
  refine all_range'_join 224 32 588 cwDegreeCheck cw_degree_chunk_007 ?_
  refine all_range'_join 256 32 556 cwDegreeCheck cw_degree_chunk_008 ?_
  refine all_range'_join 288 32 524 cwDegreeCheck cw_degree_chunk_009 ?_
  refine all_range'_join 320 32 492 cwDegreeCheck cw_degree_chunk_010 ?_
  refine all_range'_join 352 32 460 cwDegreeCheck cw_degree_chunk_011 ?_
  refine all_range'_join 384 32 428 cwDegreeCheck cw_degree_chunk_012 ?_
  refine all_range'_join 416 32 396 cwDegreeCheck cw_degree_chunk_013 ?_
  refine all_range'_join 448 32 364 cwDegreeCheck cw_degree_chunk_014 ?_
  refine all_range'_join 480 32 332 cwDegreeCheck cw_degree_chunk_015 ?_
  refine all_range'_join 512 32 300 cwDegreeCheck cw_degree_chunk_016 ?_
  refine all_range'_join 544 32 268 cwDegreeCheck cw_degree_chunk_017 ?_
  refine all_range'_join 576 32 236 cwDegreeCheck cw_degree_chunk_018 ?_
  refine all_range'_join 608 32 204 cwDegreeCheck cw_degree_chunk_019 ?_
  refine all_range'_join 640 32 172 cwDegreeCheck cw_degree_chunk_020 ?_
  refine all_range'_join 672 32 140 cwDegreeCheck cw_degree_chunk_021 ?_
  refine all_range'_join 704 32 108 cwDegreeCheck cw_degree_chunk_022 ?_
  refine all_range'_join 736 32 76 cwDegreeCheck cw_degree_chunk_023 ?_
  refine all_range'_join 768 32 44 cwDegreeCheck cw_degree_chunk_024 ?_
  refine all_range'_join 800 32 12 cwDegreeCheck cw_degree_chunk_025 ?_
  exact cw_degree_chunk_026

/-- Every image in the complete 844-entry original graph has degree shift
(0,-4), including the empty image at a negative shifted target degree. -/
theorem cw_nativeImage_mem (i : CWNuEta.Generator) :
    CWToCeta.generatorImage i ∈ Presentation.homogeneousPart
      RawData.Ceta.generatorCount RawData.Ceta.relations Ceta.generatorDegree
      (CWNuEta.generatorDegree i + (0,-4)) := by
  have h := (List.all_eq_true.mp cw_degree_all) i.val (List.mem_range.mpr i.isLt)
  simp only [cwDegreeCheck, dif_pos i.isLt] at h
  rw [← CWToCeta.imageTerms_evaluate]
  exact homogeneousModuleTermsCheck_sound _ h

/-- Conditional descent uses every original source relation and preserves
every integer homogeneous span in the unchanged full target quotient. -/
theorem cw_desc_mem
    (hrel : ∀ code ∈ RawData.CWNuEta.relations,
      Presentation.evaluateRelation CWToCeta.generatorImage code = 0)
    {d : ℤ × ℤ} {x : CWNuEta.Model}
    (hx : x ∈ Presentation.homogeneousPart RawData.CWNuEta.generatorCount
      RawData.CWNuEta.relations CWNuEta.generatorDegree d) :
    Presentation.desc CWToCeta.generatorImage RawData.CWNuEta.relations hrel x ∈
      Presentation.homogeneousPart RawData.Ceta.generatorCount RawData.Ceta.relations
        Ceta.generatorDegree (d + (0,-4)) :=
  Presentation.desc_mem_homogeneousSpan _ _ hrel _ _ cw_nativeImage_mem hx

noncomputable def cwDescAt
    (hrel : ∀ code ∈ RawData.CWNuEta.relations,
      Presentation.evaluateRelation CWToCeta.generatorImage code = 0)
    (s t : ℕ) :
    ↥(Presentation.homogeneousPart RawData.CWNuEta.generatorCount RawData.CWNuEta.relations
      CWNuEta.generatorDegree ((s : ℤ), (t : ℤ) + 4)) →ₗ[F2]
    ↥(Presentation.homogeneousPart RawData.Ceta.generatorCount RawData.Ceta.relations
      Ceta.generatorDegree ((s : ℤ), (t : ℤ))) :=
  (((Presentation.desc CWToCeta.generatorImage RawData.CWNuEta.relations hrel).restrictScalars
    F2).domRestrict _).codRestrict _ (by
      intro x
      have h := cw_desc_mem hrel x.property
      have hd : ((s : ℤ), (t : ℤ) + 4) + (0,-4) = ((s : ℤ),(t : ℤ)) := by
        ext <;> simp
      rw [hd] at h
      exact h)

theorem cwDescAt_val
    (hrel : ∀ code ∈ RawData.CWNuEta.relations,
      Presentation.evaluateRelation CWToCeta.generatorImage code = 0)
    (s t : ℕ)
    (x : ↥(Presentation.homogeneousPart RawData.CWNuEta.generatorCount RawData.CWNuEta.relations
      CWNuEta.generatorDegree ((s : ℤ), (t : ℤ) + 4))) :
    (cwDescAt hrel s t x).val =
      Presentation.desc CWToCeta.generatorImage RawData.CWNuEta.relations hrel x.val := rfl

end KIP126.LinModule.NativeMapCertificates
