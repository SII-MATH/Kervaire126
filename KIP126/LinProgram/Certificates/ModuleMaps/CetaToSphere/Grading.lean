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

theorem ceta_degree_all :
    ((List.range RawData.Ceta.generatorCount).all cetaDegreeCheck) = true := by cbv

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
