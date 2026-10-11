module

public import KIP126.LinProgram.Generated.Naturality.Row245131Map
public import KIP126.LinProgram.Certificates.Naturality.Row245131Coordinates

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Two fixed native map evaluations for log 245131. The input certificates
come from the authenticated generator-image and basis tables. Kernel checking
proves evaluation in the original sphere quotient. Descent through the complete
Ceta quotient remains explicitly conditional on all its defining relations;
no statement here identifies this graph with the actual top-cell map. -/
namespace KIP126.LinModule.Naturality245131
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open NativeMapCertificates NaturalityMapCertificate
open RawData.Naturality245131

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.toNat?_eq_chars

/-- Convert recorded coordinates to the existing sphere catalogue record type.
The database row ID is metadata; the local index is part of the coordinate. -/
def basisRow (r : BasisRecord) : BasisRow := ⟨r.s, r.t, r.localIndex, r.code⟩

theorem source_check : NaturalityMapCertificate.check sourceCertificate = true := by cbv

theorem target_check : NaturalityMapCertificate.check targetCertificate = true := by cbv

theorem source_sphere_row : basisRow sourceCertificate.target =
    NaturalityCoordinates.sourceRow := rfl

theorem target_sphere_row : basisRow targetCertificate.target =
    NaturalityCoordinates.targetRow := rfl

theorem source_sphere_row_mem : basisRow sourceCertificate.target ∈ basisRows :=
  source_sphere_row ▸ NaturalityCoordinates.sourceRow_mem

theorem target_sphere_row_mem : basisRow targetCertificate.target ∈ basisRows :=
  target_sphere_row ▸ NaturalityCoordinates.targetRow_mem

/-- Both selected words use this exact entry of the complete native graph. -/
theorem generator_one_image : generatorImage ⟨1, by decide⟩ =
    LinE2.generator ⟨0, by decide⟩ := by
  have hi : images ⟨1, by decide⟩ = [[0]] := by cbv
  rw [generatorImage, ← evaluate_parseNativeCode]
  change NamedElementCertificates.evaluate nativeScalar (images ⟨1, by decide⟩) = _
  rw [hi]
  simpa only [NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, mul_one, add_zero] using nativeScalar_eq_generator 0 (by decide)

/-- The exact source coordinates and native expressions supplied by the pinned
Ceta basis transcription. This records no claim of basis independence. -/
theorem source_module_row : sourceCertificate.source =
    (⟨69, 2, 19, 0, "7,1,1"⟩ : BasisRecord) := rfl

theorem target_module_row : targetCertificate.source =
    (⟨80, 5, 21, 0, "8,1,1"⟩ : BasisRecord) := rfl

private theorem source_image_value : nativeImage sourceCertificate.target.code =
    NaturalityCoordinates.source.val := by
  rw [NaturalityCoordinates.source_value]
  have hs : "0,1,7,1".splitOn ";" = ["0,1,7,1"] := by cbv
  simp only [sourceCertificate, nativeImage, basisValue, NaturalityCoordinates.sourceRow,
    relationPolynomial, hs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rfl

private theorem target_image_value : nativeImage targetCertificate.target.code =
    NaturalityCoordinates.target.val := by
  rw [NaturalityCoordinates.target_value]
  have hs : "0,1,8,1".splitOn ";" = ["0,1,8,1"] := by cbv
  simp only [targetCertificate, nativeImage, basisValue, NaturalityCoordinates.targetRow,
    relationPolynomial, hs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rfl

/-- Closed evaluation of the native Ceta source expression using all original
map-generator images. This is not yet a quotient map or spectrum comparison. -/
theorem source_evaluate :
    Presentation.evaluatePowers generatorImage [7, 1, 1] =
      NaturalityCoordinates.source.val := by
  have h := NaturalityMapCertificate.check_sound sourceCertificate source_check
  have hw : word sourceCertificate = [7, 1, 1] := by cbv
  rw [hw, source_image_value] at h
  exact h

/-- Closed evaluation of the native Ceta target expression in the original
sphere quotient, with the fixed (5,19)[0] coordinate. -/
theorem target_evaluate :
    Presentation.evaluatePowers generatorImage [8, 1, 1] =
      NaturalityCoordinates.target.val := by
  have h := NaturalityMapCertificate.check_sound targetCertificate target_check
  have hw : word targetCertificate = [8, 1, 1] := by cbv
  rw [hw, target_image_value] at h
  exact h

/-- If the full original relation family is certified, the resulting full
quotient map sends the fixed Ceta source to the fixed sphere source. -/
theorem source_desc
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial "7,1,1") = NaturalityCoordinates.source.val := by
  exact (NaturalityMapCertificate.check_sound_desc sourceCertificate source_check hrel).trans
    source_image_value

/-- The target computation uses the same complete graph and the same full
relation hypothesis as the source computation. -/
theorem target_desc
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial "8,1,1") = NaturalityCoordinates.target.val := by
  exact (NaturalityMapCertificate.check_sound_desc targetCertificate target_check hrel).trans
    target_image_value

end KIP126.LinModule.Naturality245131
