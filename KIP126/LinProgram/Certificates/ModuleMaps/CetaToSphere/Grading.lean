module

public import KIP126.LinProgram.Certificates.ModuleMaps.Grading
public import KIP126.LinProgram.Model.Ceta.Grading
public import KIP126.LinProgram.Generated.ModuleMaps.CetaToSphere
public import KIP126.LinProgram.Certificates.SquareDimension.Generators.Proofs

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Every generator image in the complete native Ceta-to-sphere graph has
its original bidegree shifted by (0,-2). These are homogeneous spans of the
unchanged quotients, without an assertion of direct-sum decomposition or an
actual Ext/map comparison. Descent still requires all original relations. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
namespace KIP126.LinModule.NativeMapCertificates
open KIP126.Core.Algebra
theorem cetaCode_get (i : Fin RawData.Maps.CetaToSphere.sourceGeneratorCount) :
    RawData.Maps.CetaToSphere.imageCode i =
      (RawData.Maps.CetaToSphere.rows[i.val]'(by
        have h : RawData.Maps.CetaToSphere.rows.size = RawData.Maps.CetaToSphere.sourceGeneratorCount := rfl
        simpa only [h] using i.isLt)).image := by
  simp only [RawData.Maps.CetaToSphere.imageCode, RawData.Maps.CetaToSphere.imageCodes, Array.getElem_map]

open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates NamedElementCertificates
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma
  SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

def cetaDegreeCheck (i : Nat) : Bool :=
  if h : i < RawData.Ceta.generatorCount then
    homogeneousPolynomialCheck
      (parseNativeCode (RawData.Maps.CetaToSphere.imageCode ⟨i,h⟩))
      (Ceta.generatorDegree ⟨i,h⟩ + (0,-2))
  else false

-- Keep each kernel computation small and elaborate the batches sequentially.
-- The join lemma preserves the complete original generator range.
private theorem ceta_degree_join (start left right : Nat)
    (hl : (List.range' start left).all cetaDegreeCheck = true)
    (hr : (List.range' (start + left) right).all cetaDegreeCheck = true) :
    (List.range' start (left + right)).all cetaDegreeCheck = true := by
  rw [← List.range'_append_1, List.all_append, hl, hr]; rfl

private theorem ceta_degree_chunk000 :
    (List.range' 0 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk032 :
    (List.range' 32 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk064 :
    (List.range' 64 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk096 :
    (List.range' 96 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk128 :
    (List.range' 128 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk160 :
    (List.range' 160 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk192 :
    (List.range' 192 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk224 :
    (List.range' 224 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk256 :
    (List.range' 256 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk288 :
    (List.range' 288 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk320 :
    (List.range' 320 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk352 :
    (List.range' 352 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk384 :
    (List.range' 384 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk416 :
    (List.range' 416 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk448 :
    (List.range' 448 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk480 :
    (List.range' 480 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk512 :
    (List.range' 512 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk544 :
    (List.range' 544 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk576 :
    (List.range' 576 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk608 :
    (List.range' 608 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk640 :
    (List.range' 640 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk672 :
    (List.range' 672 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk704 :
    (List.range' 704 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk736 :
    (List.range' 736 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk768 :
    (List.range' 768 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk800 :
    (List.range' 800 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk832 :
    (List.range' 832 32).all cetaDegreeCheck = true := by cbv

private theorem ceta_degree_chunk864 :
    (List.range' 864 23).all cetaDegreeCheck = true := by cbv

theorem ceta_degree_all :
    ((List.range RawData.Ceta.generatorCount).all cetaDegreeCheck) = true := by
  rw [List.range_eq_range']
  change (List.range' 0 887).all cetaDegreeCheck = true
  refine ceta_degree_join 0 32 855 ceta_degree_chunk000 ?_
  refine ceta_degree_join 32 32 823 ceta_degree_chunk032 ?_
  refine ceta_degree_join 64 32 791 ceta_degree_chunk064 ?_
  refine ceta_degree_join 96 32 759 ceta_degree_chunk096 ?_
  refine ceta_degree_join 128 32 727 ceta_degree_chunk128 ?_
  refine ceta_degree_join 160 32 695 ceta_degree_chunk160 ?_
  refine ceta_degree_join 192 32 663 ceta_degree_chunk192 ?_
  refine ceta_degree_join 224 32 631 ceta_degree_chunk224 ?_
  refine ceta_degree_join 256 32 599 ceta_degree_chunk256 ?_
  refine ceta_degree_join 288 32 567 ceta_degree_chunk288 ?_
  refine ceta_degree_join 320 32 535 ceta_degree_chunk320 ?_
  refine ceta_degree_join 352 32 503 ceta_degree_chunk352 ?_
  refine ceta_degree_join 384 32 471 ceta_degree_chunk384 ?_
  refine ceta_degree_join 416 32 439 ceta_degree_chunk416 ?_
  refine ceta_degree_join 448 32 407 ceta_degree_chunk448 ?_
  refine ceta_degree_join 480 32 375 ceta_degree_chunk480 ?_
  refine ceta_degree_join 512 32 343 ceta_degree_chunk512 ?_
  refine ceta_degree_join 544 32 311 ceta_degree_chunk544 ?_
  refine ceta_degree_join 576 32 279 ceta_degree_chunk576 ?_
  refine ceta_degree_join 608 32 247 ceta_degree_chunk608 ?_
  refine ceta_degree_join 640 32 215 ceta_degree_chunk640 ?_
  refine ceta_degree_join 672 32 183 ceta_degree_chunk672 ?_
  refine ceta_degree_join 704 32 151 ceta_degree_chunk704 ?_
  refine ceta_degree_join 736 32 119 ceta_degree_chunk736 ?_
  refine ceta_degree_join 768 32 87 ceta_degree_chunk768 ?_
  refine ceta_degree_join 800 32 55 ceta_degree_chunk800 ?_
  refine ceta_degree_join 832 32 23 ceta_degree_chunk832 ?_
  exact ceta_degree_chunk864

/-- Every image in the entire pinned native graph has the original source
bidegree shifted by (0,-2), including the zero image below suspension degree. -/
theorem ceta_nativeImage_mem (i : Ceta.Generator) :
    nativeImage (RawData.Maps.CetaToSphere.imageCode i) ∈
      coefficientPart (Ceta.generatorDegree i + (0,-2)) := by
  have h := (List.all_eq_true.mp ceta_degree_all) i.val (List.mem_range.mpr i.isLt)
  simp only [cetaDegreeCheck, dif_pos i.isLt] at h
  rw [← evaluate_parseNativeCode]
  exact homogeneousPolynomialCheck_sound _ _ h

/-- Any descent supplied with all original relation proofs preserves every
integer homogeneous span. Relation certification is still an explicit input. -/
theorem ceta_desc_mem
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation
        (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i)) code = 0)
    {d : ℤ × ℤ} {x : Ceta.Model}
    (hx : x ∈ Presentation.homogeneousPart RawData.Ceta.generatorCount
      RawData.Ceta.relations Ceta.generatorDegree d) :
    Presentation.desc
      (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i))
      RawData.Ceta.relations hrel x ∈ coefficientPart (d + (0,-2)) :=
  Presentation.desc_mem_homogeneousSpan _ _ hrel _ _ ceta_nativeImage_mem hx

noncomputable def cetaDescAt
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation
        (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i)) code = 0)
    (s t : ℕ) :
    ↥(Presentation.homogeneousPart RawData.Ceta.generatorCount RawData.Ceta.relations
      Ceta.generatorDegree ((s : ℤ), (t : ℤ) + 2)) →ₗ[F2] LinE2.E2At s t :=
  (((Presentation.desc
    (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i))
    RawData.Ceta.relations hrel).restrictScalars F2).domRestrict _).codRestrict
    (LinE2.homogeneousPart s t) (by
      intro x
      have h := ceta_desc_mem hrel x.property
      have hd : ((s : ℤ), (t : ℤ) + 2) + (0,-2) = ((s : ℤ),(t : ℤ)) := by
        ext <;> simp
      rw [hd, coefficientPart_nat] at h
      exact h)

theorem cetaDescAt_val
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation
        (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i)) code = 0)
    (s t : ℕ)
    (x : ↥(Presentation.homogeneousPart RawData.Ceta.generatorCount RawData.Ceta.relations
      Ceta.generatorDegree ((s : ℤ), (t : ℤ) + 2))) :
    (cetaDescAt hrel s t x).val =
      Presentation.desc
        (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i))
        RawData.Ceta.relations hrel x.val := rfl

end KIP126.LinModule.NativeMapCertificates
