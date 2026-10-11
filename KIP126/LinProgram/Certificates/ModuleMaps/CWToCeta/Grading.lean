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

theorem cw_degree_all :
    ((List.range RawData.CWNuEta.generatorCount).all cwDegreeCheck) = true := by cbv

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
