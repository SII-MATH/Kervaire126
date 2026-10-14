module

public import KIP126.LinProgram.Certificates.ModuleMaps.ModuleSupport
public import KIP126.LinProgram.Certificates.ModuleMaps.Support
public import KIP126.LinProgram.Model.Modules
public import KIP126.LinProgram.Generated.ModuleMaps.CWToCeta
public import KIP126.LinProgram.Tactic.LinRelation

import all Init.Data.List.SplitOn.Basic

@[expose] public section


namespace KIP126.LinModule.CWMaxSupport
open NamedElementCertificates KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinE2.NativeModuleCertificates.Support KIP126.LinModule.NativeMapCertificates
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
attribute [local cbv_eval] SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

def supportIndex : Fin 29 → Fin 887 := ![0, 1, 2, 3, 4, 9, 10, 16, 22, 24, 29, 33, 41, 46, 57, 59, 185, 198, 214, 217, 223, 228, 293, 298, 366, 385, 453, 482, 755]
def supportEmbedding : Fin 29 ↪ Fin 887 := ⟨supportIndex, by decide +kernel⟩
def fullGenerators : Fin 887 → Ceta.Model := Ceta.generator
def smallGenerators : Fin 29 → Ceta.Model := fullGenerators ∘ supportEmbedding

def rel0 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 28 [[2]]) (ModuleExpressions.add (slot 27 [[16]]) (slot 26 [[20]]))

theorem rel0_mem : "2,1,755;16,1,482;20,1,453" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 410) (by rfl))

theorem rel0_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel0 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "2,1,755;16,1,482;20,1,453" rel0_mem
  have hc : (("2,1,755;16,1,482;20,1,453".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[2, 1, 755], [16, 1, 482], [20, 1, 453]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel0, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 2 (by decide), nativeScalar_eq_generator 16 (by decide), nativeScalar_eq_generator 20 (by decide)] using hp

def rel1 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 27 [[16]]) (ModuleExpressions.add (slot 25 [[31]]) (slot 24 [[40]]))

theorem rel1_mem : "16,1,482;31,1,385;40,1,366" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 416) (by rfl))

theorem rel1_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel1 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "16,1,482;31,1,385;40,1,366" rel1_mem
  have hc : (("16,1,482;31,1,385;40,1,366".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[16, 1, 482], [31, 1, 385], [40, 1, 366]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel1, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 16 (by decide), nativeScalar_eq_generator 31 (by decide), nativeScalar_eq_generator 40 (by decide)] using hp

def rel2 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 26 [[20]]) (ModuleExpressions.add (slot 24 [[40]]) (ModuleExpressions.add (slot 22 [[53]]) (slot 21 [[64]])))

theorem rel2_mem : "20,1,453;40,1,366;53,1,293;64,1,228" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 423) (by rfl))

theorem rel2_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel2 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "20,1,453;40,1,366;53,1,293;64,1,228" rel2_mem
  have hc : (("20,1,453;40,1,366;53,1,293;64,1,228".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[20, 1, 453], [40, 1, 366], [53, 1, 293], [64, 1, 228]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel2, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 20 (by decide), nativeScalar_eq_generator 40 (by decide), nativeScalar_eq_generator 53 (by decide), nativeScalar_eq_generator 64 (by decide)] using hp

def rel3 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 25 [[31]]) (slot 23 [[50]])

theorem rel3_mem : "31,1,385;50,1,298" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 419) (by rfl))

theorem rel3_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel3 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "31,1,385;50,1,298" rel3_mem
  have hc : (("31,1,385;50,1,298".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[31, 1, 385], [50, 1, 298]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel3, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 31 (by decide), nativeScalar_eq_generator 50 (by decide)] using hp

def rel4 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 23 [[50]]) (slot 19 [[71]])

theorem rel4_mem : "50,1,298;71,1,217" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 425) (by rfl))

theorem rel4_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel4 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "50,1,298;71,1,217" rel4_mem
  have hc : (("50,1,298;71,1,217".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[50, 1, 298], [71, 1, 217]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel4, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 50 (by decide), nativeScalar_eq_generator 71 (by decide)] using hp

def rel5 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 22 [[53]]) (ModuleExpressions.add (slot 20 [[66]]) (slot 18 [[72]]))

theorem rel5_mem : "53,1,293;66,1,223;72,1,214" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 426) (by rfl))

theorem rel5_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel5 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "53,1,293;66,1,223;72,1,214" rel5_mem
  have hc : (("53,1,293;66,1,223;72,1,214".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[53, 1, 293], [66, 1, 223], [72, 1, 214]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel5, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 53 (by decide), nativeScalar_eq_generator 66 (by decide), nativeScalar_eq_generator 72 (by decide)] using hp

def rel6 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 21 [[64]]) (ModuleExpressions.add (slot 20 [[66]]) (slot 17 [[79]]))

theorem rel6_mem : "64,1,228;66,1,223;79,1,198" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 427) (by rfl))

theorem rel6_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel6 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "64,1,228;66,1,223;79,1,198" rel6_mem
  have hc : (("64,1,228;66,1,223;79,1,198".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[64, 1, 228], [66, 1, 223], [79, 1, 198]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel6, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 64 (by decide), nativeScalar_eq_generator 66 (by decide), nativeScalar_eq_generator 79 (by decide)] using hp

def rel7 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 19 [[71]]) (ModuleExpressions.add (slot 18 [[72]]) (ModuleExpressions.add (slot 17 [[79]]) (ModuleExpressions.add (slot 16 [[90]]) (slot 16 [[89]]))))

theorem rel7_mem : "71,1,217;72,1,214;79,1,198;90,1,185;89,1,185" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 429) (by rfl))

theorem rel7_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel7 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "71,1,217;72,1,214;79,1,198;90,1,185;89,1,185" rel7_mem
  have hc : (("71,1,217;72,1,214;79,1,198;90,1,185;89,1,185".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[71, 1, 217], [72, 1, 214], [79, 1, 198], [90, 1, 185], [89, 1, 185]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel7, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 71 (by decide), nativeScalar_eq_generator 72 (by decide), nativeScalar_eq_generator 79 (by decide), nativeScalar_eq_generator 89 (by decide), nativeScalar_eq_generator 90 (by decide)] using hp

def rel8 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 17 [[79]]) (ModuleExpressions.add (slot 15 [[274]]) (ModuleExpressions.add (slot 13 [[327]]) (ModuleExpressions.add (slot 12 [[366]]) (ModuleExpressions.add (slot 11 [[434]]) (slot 10 [[449]])))))

theorem rel8_mem : "79,1,198;274,1,59;327,1,46;366,1,41;434,1,33;449,1,29" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 445) (by rfl))

theorem rel8_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel8 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "79,1,198;274,1,59;327,1,46;366,1,41;434,1,33;449,1,29" rel8_mem
  have hc : (("79,1,198;274,1,59;327,1,46;366,1,41;434,1,33;449,1,29".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[79, 1, 198], [274, 1, 59], [327, 1, 46], [366, 1, 41], [434, 1, 33], [449, 1, 29]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel8, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 79 (by decide), nativeScalar_eq_generator 274 (by decide), nativeScalar_eq_generator 327 (by decide), nativeScalar_eq_generator 366 (by decide), nativeScalar_eq_generator 434 (by decide), nativeScalar_eq_generator 449 (by decide)] using hp

def rel9 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 16 [[89]]) (ModuleExpressions.add (slot 14 [[278]]) (slot 13 [[327]]))

theorem rel9_mem : "89,1,185;278,1,57;327,1,46" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 440) (by rfl))

theorem rel9_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel9 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "89,1,185;278,1,57;327,1,46" rel9_mem
  have hc : (("89,1,185;278,1,57;327,1,46".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[89, 1, 185], [278, 1, 57], [327, 1, 46]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel9, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 89 (by decide), nativeScalar_eq_generator 278 (by decide), nativeScalar_eq_generator 327 (by decide)] using hp

def rel10 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 15 [[274]]) (ModuleExpressions.add (slot 13 [[327]]) (ModuleExpressions.add (slot 11 [[434]]) (slot 8 [[539]])))

theorem rel10_mem : "274,1,59;327,1,46;434,1,33;539,1,22" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 448) (by rfl))

theorem rel10_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel10 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "274,1,59;327,1,46;434,1,33;539,1,22" rel10_mem
  have hc : (("274,1,59;327,1,46;434,1,33;539,1,22".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[274, 1, 59], [327, 1, 46], [434, 1, 33], [539, 1, 22]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel10, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 274 (by decide), nativeScalar_eq_generator 327 (by decide), nativeScalar_eq_generator 434 (by decide), nativeScalar_eq_generator 539 (by decide)] using hp

def rel11 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 14 [[278]]) (ModuleExpressions.add (slot 13 [[327]]) (slot 11 [[434]]))

theorem rel11_mem : "278,1,57;327,1,46;434,1,33" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 443) (by rfl))

theorem rel11_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel11 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "278,1,57;327,1,46;434,1,33" rel11_mem
  have hc : (("278,1,57;327,1,46;434,1,33".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[278, 1, 57], [327, 1, 46], [434, 1, 33]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel11, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 278 (by decide), nativeScalar_eq_generator 327 (by decide), nativeScalar_eq_generator 434 (by decide)] using hp

def rel12 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 12 [[366]]) (slot 9 [[502]])

theorem rel12_mem : "366,1,41;502,1,24" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 447) (by rfl))

theorem rel12_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel12 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "366,1,41;502,1,24" rel12_mem
  have hc : (("366,1,41;502,1,24".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[366, 1, 41], [502, 1, 24]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel12, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 366 (by decide), nativeScalar_eq_generator 502 (by decide)] using hp

def rel13 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 11 [[434]]) (ModuleExpressions.add (slot 10 [[449]]) (ModuleExpressions.add (slot 8 [[539]]) (ModuleExpressions.add (slot 7 [[612]]) (slot 5 [[704]]))))

theorem rel13_mem : "434,1,33;449,1,29;539,1,22;612,1,16;704,1,9" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 452) (by rfl))

theorem rel13_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel13 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "434,1,33;449,1,29;539,1,22;612,1,16;704,1,9" rel13_mem
  have hc : (("434,1,33;449,1,29;539,1,22;612,1,16;704,1,9".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[434, 1, 33], [449, 1, 29], [539, 1, 22], [612, 1, 16], [704, 1, 9]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel13, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 434 (by decide), nativeScalar_eq_generator 449 (by decide), nativeScalar_eq_generator 539 (by decide), nativeScalar_eq_generator 612 (by decide), nativeScalar_eq_generator 704 (by decide)] using hp

def rel14 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 9 [[502]]) (slot 7 [[612]])

theorem rel14_mem : "502,1,24;612,1,16" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 450) (by rfl))

theorem rel14_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel14 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "502,1,24;612,1,16" rel14_mem
  have hc : (("502,1,24;612,1,16".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[502, 1, 24], [612, 1, 16]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel14, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 502 (by decide), nativeScalar_eq_generator 612 (by decide)] using hp

def rel15 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 6 [[2]]) (ModuleExpressions.add (slot 3 [[9]]) (slot 2 [[17]]))

theorem rel15_mem : "2,1,10;9,1,3;17,1,2" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 0 (by decide) _
    (List.mem_of_getElem? (i := 84) (by rfl))

theorem rel15_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel15 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "2,1,10;9,1,3;17,1,2" rel15_mem
  have hc : (("2,1,10;9,1,3;17,1,2".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[2, 1, 10], [9, 1, 3], [17, 1, 2]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel15, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 2 (by decide), nativeScalar_eq_generator 9 (by decide), nativeScalar_eq_generator 17 (by decide)] using hp

def rel16 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 5 [[704]]) (slot 4 [[854]])

theorem rel16_mem : "704,1,9;854,1,4" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 455) (by rfl))

theorem rel16_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel16 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "704,1,9;854,1,4" rel16_mem
  have hc : (("704,1,9;854,1,4".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[704, 1, 9], [854, 1, 4]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel16, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 704 (by decide), nativeScalar_eq_generator 854 (by decide)] using hp

def rel17 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 4 [[854]]) (slot 1 [[8, 812]])

theorem rel17_mem : "854,1,4;8,1,812,1,1" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 457) (by rfl))

theorem rel17_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel17 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "854,1,4;8,1,812,1,1" rel17_mem
  have hc : (("854,1,4;8,1,812,1,1".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[854, 1, 4], [8, 1, 812, 1, 1]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel17, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 8 (by decide), nativeScalar_eq_generator 812 (by decide), nativeScalar_eq_generator 854 (by decide)] using hp

def rel18 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 3 [[9]]) (slot 0 [[8, 8]])

theorem rel18_mem : "9,1,3;8,2,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 0 (by decide) _
    (List.mem_of_getElem? (i := 86) (by rfl))

theorem rel18_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel18 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "9,1,3;8,2,0" rel18_mem
  have hc : (("9,1,3;8,2,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[9, 1, 3], [8, 2, 0]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel18, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 8 (by decide), nativeScalar_eq_generator 9 (by decide)] using hp

def rel19 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 2 [[9]]) (slot 1 [[13]])

theorem rel19_mem : "9,1,2;13,1,1" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 0 (by decide) _
    (List.mem_of_getElem? (i := 42) (by rfl))

theorem rel19_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel19 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "9,1,2;13,1,1" rel19_mem
  have hc : (("9,1,2;13,1,1".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[9, 1, 2], [13, 1, 1]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel19, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 9 (by decide), nativeScalar_eq_generator 13 (by decide)] using hp

def rel20 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 1 [[13, 23]]) (slot 0 [[9, 32]])

theorem rel20_mem : "13,1,23,1,1;9,1,32,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 1 (by decide) _
    (List.mem_of_getElem? (i := 53) (by rfl))

theorem rel20_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel20 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "13,1,23,1,1;9,1,32,1,0" rel20_mem
  have hc : (("13,1,23,1,1;9,1,32,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[13, 1, 23, 1, 1], [9, 1, 32, 1, 0]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel20, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 9 (by decide), nativeScalar_eq_generator 13 (by decide), nativeScalar_eq_generator 23 (by decide), nativeScalar_eq_generator 32 (by decide)] using hp

def rel21 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 1 [[8, 812]]) (slot 0 [[16, 64, 188]])

theorem rel21_mem : "8,1,812,1,1;16,1,64,1,188,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 129 (by decide) _
    (List.mem_of_getElem? (i := 461) (by rfl))

theorem rel21_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel21 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "8,1,812,1,1;16,1,64,1,188,1,0" rel21_mem
  have hc : (("8,1,812,1,1;16,1,64,1,188,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[8, 1, 812, 1, 1], [16, 1, 64, 1, 188, 1, 0]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel21, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 8 (by decide), nativeScalar_eq_generator 16 (by decide), nativeScalar_eq_generator 64 (by decide), nativeScalar_eq_generator 188 (by decide), nativeScalar_eq_generator 812 (by decide)] using hp

def rel22 : ModuleExpressions.Expression 29 := slot 0 [[79, 299], [72, 327]]

theorem rel22_mem : "79,1,299,1;72,1,327,1" ∈ KIP126.LinE2.RawData.relations := by
  lin_relation 51 "79,1,299,1;72,1,327,1"

theorem rel22_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel22 = 0 := by
  have hc : parseNativeCode "79,1,299,1;72,1,327,1" = [[79, 299], [72, 327]] := by cbv
  have hz : NamedElementCertificates.evaluate nativeScalar [[79, 299], [72, 327]] = 0 := by
    rw [← hc, evaluate_parseNativeCode]
    simpa only [nativeImage, if_neg (show "79,1,299,1;72,1,327,1" ≠ "" from by decide)] using csv_relation_zero "79,1,299,1;72,1,327,1" rel22_mem
  rw [rel22, evaluate_slot, hz]
  exact zero_smul E2 (smallGenerators 0)

def rel23 : ModuleExpressions.Expression 29 := slot 0 [[72, 327], [16, 64, 188]]

theorem rel23_mem : "72,1,327,1;16,1,64,1,188,1" ∈ KIP126.LinE2.RawData.relations := by
  lin_relation 51 "72,1,327,1;16,1,64,1,188,1"

theorem rel23_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel23 = 0 := by
  have hc : parseNativeCode "72,1,327,1;16,1,64,1,188,1" = [[72, 327], [16, 64, 188]] := by cbv
  have hz : NamedElementCertificates.evaluate nativeScalar [[72, 327], [16, 64, 188]] = 0 := by
    rw [← hc, evaluate_parseNativeCode]
    simpa only [nativeImage, if_neg (show "72,1,327,1;16,1,64,1,188,1" ≠ "" from by decide)] using csv_relation_zero "72,1,327,1;16,1,64,1,188,1" rel23_mem
  rw [rel23, evaluate_slot, hz]
  exact zero_smul E2 (smallGenerators 0)

def rel24 : ModuleExpressions.Expression 29 := slot 0 [[9, 17], [8, 20]]

theorem rel24_mem : "9,1,17,1;8,1,20,1" ∈ KIP126.LinE2.RawData.relations := by
  lin_relation 0 "9,1,17,1;8,1,20,1"

theorem rel24_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel24 = 0 := by
  have hc : parseNativeCode "9,1,17,1;8,1,20,1" = [[9, 17], [8, 20]] := by cbv
  have hz : NamedElementCertificates.evaluate nativeScalar [[9, 17], [8, 20]] = 0 := by
    rw [← hc, evaluate_parseNativeCode]
    simpa only [nativeImage, if_neg (show "9,1,17,1;8,1,20,1" ≠ "" from by decide)] using csv_relation_zero "9,1,17,1;8,1,20,1" rel24_mem
  rw [rel24, evaluate_slot, hz]
  exact zero_smul E2 (smallGenerators 0)

def rel25 : ModuleExpressions.Expression 29 := slot 0 [[20, 32], [13, 45]]

theorem rel25_mem : "20,1,32,1;13,1,45,1" ∈ KIP126.LinE2.RawData.relations := by
  lin_relation 0 "20,1,32,1;13,1,45,1"

theorem rel25_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel25 = 0 := by
  have hc : parseNativeCode "20,1,32,1;13,1,45,1" = [[20, 32], [13, 45]] := by cbv
  have hz : NamedElementCertificates.evaluate nativeScalar [[20, 32], [13, 45]] = 0 := by
    rw [← hc, evaluate_parseNativeCode]
    simpa only [nativeImage, if_neg (show "20,1,32,1;13,1,45,1" ≠ "" from by decide)] using csv_relation_zero "20,1,32,1;13,1,45,1" rel25_mem
  rw [rel25, evaluate_slot, hz]
  exact zero_smul E2 (smallGenerators 0)

def rel26 : ModuleExpressions.Expression 29 := slot 0 [[13, 45], [8, 9, 23]]

theorem rel26_mem : "13,1,45,1;8,1,9,1,23,1" ∈ KIP126.LinE2.RawData.relations := by
  lin_relation 0 "13,1,45,1;8,1,9,1,23,1"

theorem rel26_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel26 = 0 := by
  have hc : parseNativeCode "13,1,45,1;8,1,9,1,23,1" = [[13, 45], [8, 9, 23]] := by cbv
  have hz : NamedElementCertificates.evaluate nativeScalar [[13, 45], [8, 9, 23]] = 0 := by
    rw [← hc, evaluate_parseNativeCode]
    simpa only [nativeImage, if_neg (show "13,1,45,1;8,1,9,1,23,1" ≠ "" from by decide)] using csv_relation_zero "13,1,45,1;8,1,9,1,23,1" rel26_mem
  rw [rel26, evaluate_slot, hz]
  exact zero_smul E2 (smallGenerators 0)

def rel27 : ModuleExpressions.Expression 29 := slot 0 [[0, 0, 2]]

theorem rel27_mem : "0,2,2,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 0 (by decide) _
    (List.mem_of_getElem? (i := 2) (by rfl))

theorem rel27_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel27 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "0,2,2,1,0" rel27_mem
  have hc : (("0,2,2,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[0, 2, 2, 1, 0]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel27, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 0 (by decide), nativeScalar_eq_generator 2 (by decide)] using hp

def rel28 : ModuleExpressions.Expression 29 := slot 0 [[0, 0, 2]]

theorem rel28_mem : "0,2,2,1,0" ∈ RawData.Ceta.relations :=
  Presentation.relation_mem_of_chunk RawData.Ceta.relationChunks 0 (by decide) _
    (List.mem_of_getElem? (i := 2) (by rfl))

theorem rel28_zero : ModuleExpressions.evaluate nativeScalar smallGenerators rel28 = 0 := by
  have hp := Presentation.native_relation_zero 887 RawData.Ceta.relations "0,2,2,1,0" rel28_mem
  have hc : (("0,2,2,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[0, 2, 2, 1, 0]] := by cbv
  rw [projection_relation_words, hc] at hp
  simpa [rel28, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    mul_smul, pow_two,
    nativeScalar_eq_generator 0 (by decide), nativeScalar_eq_generator 2 (by decide)] using hp

def image187 : ModuleExpressions.Expression 29 := slot 16 [[]]

def image196 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 17 [[]]) (slot 0 [[299]])

def image766 : ModuleExpressions.Expression 29 := ModuleExpressions.add (slot 28 [[]]) (ModuleExpressions.add (slot 6 [[9, 23, 188]]) (ModuleExpressions.add (slot 0 [[0, 0, 0, 977]]) (slot 0 [[0, 0, 0, 976]])))

def input : ModuleExpressions.Expression 29 :=
  ModuleExpressions.add (ModuleExpressions.scale [[2]] image766)
    (ModuleExpressions.add (ModuleExpressions.scale [[79]] image196)
      (ModuleExpressions.scale [[90]] image187))
def rels : List (ModuleExpressions.Expression 29) := [rel0, rel1, rel2, rel3, rel4, rel5, rel6, rel7, rel8, rel9, rel10, rel11, rel12, rel13, rel14, rel15, rel16, rel17, rel18, rel19, rel20, rel21, rel22, rel23, rel24, rel25, rel26, rel27, rel28]
def witness : List Term := [
  ⟨0, [[]]⟩,
  ⟨1, [[]]⟩,
  ⟨2, [[]]⟩,
  ⟨3, [[]]⟩,
  ⟨4, [[]]⟩,
  ⟨5, [[]]⟩,
  ⟨6, [[]]⟩,
  ⟨7, [[]]⟩,
  ⟨8, [[]]⟩,
  ⟨9, [[]]⟩,
  ⟨10, [[]]⟩,
  ⟨11, [[]]⟩,
  ⟨12, [[]]⟩,
  ⟨13, [[]]⟩,
  ⟨14, [[]]⟩,
  ⟨15, [[9, 23, 188]]⟩,
  ⟨16, [[]]⟩,
  ⟨17, [[]]⟩,
  ⟨18, [[9, 23, 188]]⟩,
  ⟨19, [[17, 23, 188]]⟩,
  ⟨20, [[17, 188]]⟩,
  ⟨21, [[]]⟩,
  ⟨22, [[]]⟩,
  ⟨23, [[]]⟩,
  ⟨24, [[32, 188]]⟩,
  ⟨25, [[8, 188]]⟩,
  ⟨26, [[8, 188]]⟩,
  ⟨27, [[0, 977]]⟩,
  ⟨28, [[0, 976]]⟩]

theorem checker : ModuleExpressions.check rels input ModuleExpressions.zero witness = true := by
  decide +kernel

theorem relation_values : ∀ r ∈ rels, ModuleExpressions.evaluate nativeScalar smallGenerators r = 0 := by
  intro r hr
  simp only [rels, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rel0_zero
  · exact rel1_zero
  · exact rel2_zero
  · exact rel3_zero
  · exact rel4_zero
  · exact rel5_zero
  · exact rel6_zero
  · exact rel7_zero
  · exact rel8_zero
  · exact rel9_zero
  · exact rel10_zero
  · exact rel11_zero
  · exact rel12_zero
  · exact rel13_zero
  · exact rel14_zero
  · exact rel15_zero
  · exact rel16_zero
  · exact rel17_zero
  · exact rel18_zero
  · exact rel19_zero
  · exact rel20_zero
  · exact rel21_zero
  · exact rel22_zero
  · exact rel23_zero
  · exact rel24_zero
  · exact rel25_zero
  · exact rel26_zero
  · exact rel27_zero
  · exact rel28_zero

theorem full_887_equality :
    ModuleExpressions.evaluate nativeScalar fullGenerators (embed supportEmbedding input) = 0 := by
  have h := check_sound_embed_projection nativeVariable fullGenerators supportEmbedding rels input
    ModuleExpressions.zero witness checker (by
      intro r hr
      rw [evaluate_embed]
      exact relation_values r hr)
  change ModuleExpressions.evaluate nativeScalar fullGenerators (embed supportEmbedding input) =
    ModuleExpressions.evaluate nativeScalar fullGenerators (embed supportEmbedding ModuleExpressions.zero) at h
  rw [evaluate_embed nativeScalar fullGenerators supportEmbedding ModuleExpressions.zero,
    ModuleExpressions.evaluate_zero] at h
  exact h

end
end KIP126.LinModule.CWMaxSupport

namespace KIP126.LinModule.CWMaxSupport
open NamedElementCertificates KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinE2.NativeModuleCertificates.Support
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
attribute [local cbv_eval] SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

theorem image187_projection : ModuleExpressions.evaluate nativeScalar smallGenerators image187 =
    nativeModuleImage 887 RawData.Ceta.relations "185" := by
  have hc : (("185".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[185]] := by cbv
  rw [nativeModuleImage, if_neg (show "185" ≠ "" from by decide), projection_relation_words, hc]
  simp [image187, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers,
    ]

theorem native_image187 : RawData.Maps.CWToCeta.imageCode ⟨187, by decide⟩ = "185" := by
  simp only [RawData.Maps.CWToCeta.imageCode, RawData.Maps.CWToCeta.imageCodes, Array.getElem_map]
  rfl

theorem image196_projection : ModuleExpressions.evaluate nativeScalar smallGenerators image196 =
    nativeModuleImage 887 RawData.Ceta.relations "198;299,1,0" := by
  have hc : (("198;299,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[198], [299, 1, 0]] := by cbv
  rw [nativeModuleImage, if_neg (show "198;299,1,0" ≠ "" from by decide), projection_relation_words, hc]
  simp [image196, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount, pow_succ,
    nativeScalar_eq_generator 299 (by decide)]

theorem native_image196 : RawData.Maps.CWToCeta.imageCode ⟨196, by decide⟩ = "198;299,1,0" := by
  simp only [RawData.Maps.CWToCeta.imageCode, RawData.Maps.CWToCeta.imageCodes, Array.getElem_map]
  rfl

theorem image766_projection : ModuleExpressions.evaluate nativeScalar smallGenerators image766 =
    nativeModuleImage 887 RawData.Ceta.relations "755;9,1,23,1,188,1,10;0,3,977,1,0;0,3,976,1,0" := by
  have hc : (("755;9,1,23,1,188,1,10;0,3,977,1,0;0,3,976,1,0".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[755], [9, 1, 23, 1, 188, 1, 10], [0, 3, 977, 1, 0], [0, 3, 976, 1, 0]] := by cbv
  rw [nativeModuleImage, if_neg (show "755;9,1,23,1,188,1,10;0,3,977,1,0;0,3,976,1,0" ≠ "" from by decide), projection_relation_words, hc]
  simp [image766, ModuleExpressions.evaluate_add, evaluate_slot, smallGenerators,
    fullGenerators, supportEmbedding, supportIndex, Ceta.generator, Ceta.Model, RawData.Ceta.generatorCount,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount, mul_smul, pow_succ,
    nativeScalar_eq_generator 0 (by decide), nativeScalar_eq_generator 9 (by decide), nativeScalar_eq_generator 23 (by decide), nativeScalar_eq_generator 188 (by decide), nativeScalar_eq_generator 976 (by decide), nativeScalar_eq_generator 977 (by decide)]

theorem native_image766 : RawData.Maps.CWToCeta.imageCode ⟨766, by decide⟩ = "755;9,1,23,1,188,1,10;0,3,977,1,0;0,3,976,1,0" := by
  simp only [RawData.Maps.CWToCeta.imageCode, RawData.Maps.CWToCeta.imageCodes, Array.getElem_map]
  rfl

theorem source_relation_mem : "2,1,766;79,1,196;90,1,187" ∈ RawData.CWNuEta.relations :=
  Presentation.relation_mem_of_chunk RawData.CWNuEta.relationChunks 130 (by decide) _
    (List.mem_of_getElem? (i := 467) (by rfl))

/-- The fixed graph uses the complete original Ceta quotient. Empty native
images denote zero; no unknown or missing image can be supplied by this typed graph. -/
def cwImages (i : CWNuEta.Generator) : Ceta.Model :=
  nativeModuleImage 887 RawData.Ceta.relations (RawData.Maps.CWToCeta.imageCode i)

/-- One complete original source relation, checked through its 29-coordinate
support but evaluated in the original full 887-generator target quotient. -/
theorem row67028_image_zero : Presentation.evaluateRelation cwImages "2,1,766;79,1,196;90,1,187" = 0 := by
  have h := full_887_equality
  rw [evaluate_embed] at h
  change ModuleExpressions.evaluate nativeScalar smallGenerators input = 0 at h
  simp only [input, ModuleExpressions.evaluate_add, ModuleExpressions.evaluate_scale,
    image766_projection, image196_projection, image187_projection,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.sum_cons, List.sum_nil, mul_one, add_zero,
    nativeScalar_eq_generator 2 (by decide), nativeScalar_eq_generator 79 (by decide),
    nativeScalar_eq_generator 90 (by decide)] at h
  have hp : (("2,1,766;79,1,196;90,1,187".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
      [[2, 1, 766], [79, 1, 196], [90, 1, 187]] := by cbv
  suffices hh : (((("2,1,766;79,1,196;90,1,187".splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)).map
      (Presentation.evaluatePowers cwImages)).sum) = 0 by
    simpa only [Presentation.evaluateRelation, List.map_map, Function.comp_def] using hh
  rw [hp]
  have h766 : RawData.Maps.CWToCeta.imageCode (766 : Fin 844) = "755;9,1,23,1,188,1,10;0,3,977,1,0;0,3,976,1,0" := native_image766
  have h196 : RawData.Maps.CWToCeta.imageCode (196 : Fin 844) = "198;299,1,0" := native_image196
  have h187 : RawData.Maps.CWToCeta.imageCode (187 : Fin 844) = "185" := native_image187
  simpa [Presentation.evaluatePowers, KIP126.LinE2.RawData.generatorCount,
    RawData.CWNuEta.generatorCount, cwImages, h766, h196, h187] using h

theorem source_relation_row : RawData.CWNuEta.relationRow 67027 =
    some ⟨67028, "2,1,766;79,1,196;90,1,187", 29, 199⟩ := rfl

theorem native_empty_image : nativeModuleImage 887 RawData.Ceta.relations "" = 0 := rfl

end
end KIP126.LinModule.CWMaxSupport
