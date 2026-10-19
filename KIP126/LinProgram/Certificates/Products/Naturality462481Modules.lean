module

public import KIP126.LinProgram.Model.Modules
public import KIP126.LinProgram.Certificates.NativeModuleCertificates

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Products/Naturality462481Modules

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Closed reductions in the complete archived Ceta and CW_nu_eta modules.
Their coefficient ring is the original LinE2.E2. Every archived module
relation is included; neither an Ext comparison nor a native log label is
used as a hypothesis. Actual maps and differentials remain separate. -/
namespace KIP126.LinModule.NaturalityModuleProducts

set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- SQLite rowid 13125, with its original three terms. -/
theorem ceta13125_mem :
    "195,1,12;385,1,2;456,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 25 (by decide) _
    (List.mem_of_getElem? (i := 324) (by rfl))

/-- SQLite rowid 13126, with its original three terms. -/
theorem ceta13126_mem :
    "385,1,2;456,1,0;67,1,107,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 25 (by decide) _
    (List.mem_of_getElem? (i := 325) (by rfl))

/-- SQLite rowid 13675, with its original three terms. -/
theorem cw13675_mem :
    "3,1,240;438,1,2;0,2,418,1,2" ∈ RawData.CWNuEta.relations :=
  Presentation.relation_mem_of_chunk RawData.CWNuEta.relationChunks 26 (by decide) _
    (List.mem_of_getElem? (i := 362) (by rfl))

/-- Native reduction of the extra CW-to-Ceta matrix column. This equality
is in the full recorded module presentation, not an assertion about an
actual spectral-sequence map. -/
theorem native_ceta_map_column0 :
    LinE2.generator ⟨195, by decide⟩ • Ceta.generator ⟨12, by decide⟩ =
      (LinE2.generator ⟨67, by decide⟩ * LinE2.generator ⟨107, by decide⟩) •
        Ceta.generator ⟨0, by decide⟩ :=
  LinE2.NativeModuleCertificates.ceta_quotient_equality RawData.Ceta.relations
    ceta13125_mem ceta13126_mem

/-- Native CW module reduction used when reconstructing a prior differential
input. The reduction alone proves neither that differential nor a log edge. -/
theorem native_cw_ancestor_product :
    LinE2.generator ⟨3, by decide⟩ • CWNuEta.generator ⟨240, by decide⟩ =
      LinE2.generator ⟨438, by decide⟩ • CWNuEta.generator ⟨2, by decide⟩ +
      (LinE2.generator ⟨0, by decide⟩ ^ 2 * LinE2.generator ⟨418, by decide⟩) •
        CWNuEta.generator ⟨2, by decide⟩ :=
  LinE2.NativeModuleCertificates.cw_quotient_equality RawData.CWNuEta.relations
    cw13675_mem

attribute [local cbv_eval] LinE2.SquareDetection.splitOn_comma
  LinE2.SquareDetection.toNat?_eq_chars

/-- The same closed Ceta target in native monomial-string notation. -/
theorem native_ceta_strings :
    Ceta.monomial "195,1,12" = Ceta.monomial "67,1,107,1,0" := by
  have h₁ : ("195,1,12".splitOn ",").map (fun a => a.toNat?.getD 0) =
      [195, 1, 12] := by cbv
  have h₂ : ("67,1,107,1,0".splitOn ",").map (fun a => a.toNat?.getD 0) =
      [67, 1, 107, 1, 0] := by cbv
  unfold Ceta.monomial Presentation.monomialVector
  rw [h₁, h₂, Presentation.projection_ofPowers, Presentation.projection_ofPowers]
  have h := native_ceta_map_column0
  rw [← smul_smul] at h
  simpa [Presentation.evaluatePowers,
    LinE2.RawData.generatorCount, RawData.Ceta.generatorCount, Ceta.generator] using h

/-- The same closed CW target in native monomial-string notation. -/
theorem native_cw_strings :
    CWNuEta.monomial "3,1,240" =
      CWNuEta.monomial "438,1,2" + CWNuEta.monomial "0,2,418,1,2" := by
  have h₁ : ("3,1,240".splitOn ",").map (fun a => a.toNat?.getD 0) =
      [3, 1, 240] := by cbv
  have h₂ : ("438,1,2".splitOn ",").map (fun a => a.toNat?.getD 0) =
      [438, 1, 2] := by cbv
  have h₃ : ("0,2,418,1,2".splitOn ",").map (fun a => a.toNat?.getD 0) =
      [0, 2, 418, 1, 2] := by cbv
  unfold CWNuEta.monomial Presentation.monomialVector
  rw [h₁, h₂, h₃, Presentation.projection_ofPowers,
    Presentation.projection_ofPowers, Presentation.projection_ofPowers]
  have h := native_cw_ancestor_product
  rw [← smul_smul] at h
  simpa [Presentation.evaluatePowers,
    LinE2.RawData.generatorCount, RawData.CWNuEta.generatorCount,
    CWNuEta.generator] using h

end KIP126.LinModule.NaturalityModuleProducts
