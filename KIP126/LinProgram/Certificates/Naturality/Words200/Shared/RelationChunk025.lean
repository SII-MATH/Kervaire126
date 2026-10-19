module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk025
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
open Lean Elab Tactic in
private def block0 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[25]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 25 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[25]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block9_mem : block9 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 9) (by decide)
private theorem block9_in_rows (r : List Char) (hr : r ∈ block9) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block9, block9_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block19_mem : block19 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 19) (by decide)
private theorem block19_in_rows (r : List Char) (hr : r ∈ block19) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block19, block19_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
theorem relation1068_mem : "17,1,435,1;8,2,16,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block0[20]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1068_zero : nativeImage "17,1,435,1;8,2,16,1,187,1" = 0 := by
  change projection (relationPolynomial "17,1,435,1;8,2,16,1,187,1") = 0
  exact csv_relation_zero _ relation1068_mem
theorem relation1069_mem : "17,1,434,1;16,1,435,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[1]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1069_zero : nativeImage "17,1,434,1;16,1,435,1" = 0 := by
  change projection (relationPolynomial "17,1,434,1;16,1,435,1") = 0
  exact csv_relation_zero _ relation1069_mem
theorem relation1070_mem : "16,1,435,1;8,1,559,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[4]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1070_zero : nativeImage "16,1,435,1;8,1,559,1" = 0 := by
  change projection (relationPolynomial "16,1,435,1;8,1,559,1") = 0
  exact csv_relation_zero _ relation1070_mem
theorem relation1071_mem : "8,1,558,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[5]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1071_zero : nativeImage "8,1,558,1" = 0 := by
  change projection (relationPolynomial "8,1,558,1") = 0
  exact csv_relation_zero _ relation1071_mem
theorem relation1072_mem : "113,1,147,1;56,1,226,1;19,1,404,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[15]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1072_zero : nativeImage "113,1,147,1;56,1,226,1;19,1,404,1" = 0 := by
  change projection (relationPolynomial "113,1,147,1;56,1,226,1;19,1,404,1") = 0
  exact csv_relation_zero _ relation1072_mem
theorem relation1073_mem : "19,1,404,1;16,1,434,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[16]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1073_zero : nativeImage "19,1,404,1;16,1,434,1" = 0 := by
  change projection (relationPolynomial "19,1,404,1;16,1,434,1") = 0
  exact csv_relation_zero _ relation1073_mem
theorem relation1074_mem : "56,1,226,1;15,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[17]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1074_zero : nativeImage "56,1,226,1;15,1,454,1" = 0 := by
  change projection (relationPolynomial "56,1,226,1;15,1,454,1") = 0
  exact csv_relation_zero _ relation1074_mem
theorem relation1075_mem : "15,1,454,1;10,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[18]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1075_zero : nativeImage "15,1,454,1;10,1,516,1" = 0 := by
  change projection (relationPolynomial "15,1,454,1;10,1,516,1") = 0
  exact csv_relation_zero _ relation1075_mem
theorem relation1076_mem : "16,1,434,1;9,1,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[19]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1076_zero : nativeImage "16,1,434,1;9,1,529,1" = 0 := by
  change projection (relationPolynomial "16,1,434,1;9,1,529,1") = 0
  exact csv_relation_zero _ relation1076_mem
theorem relation1077_mem : "10,1,516,1;9,1,529,1;8,1,557,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[20]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1077_zero : nativeImage "10,1,516,1;9,1,529,1;8,1,557,1" = 0 := by
  change projection (relationPolynomial "10,1,516,1;9,1,529,1;8,1,557,1") = 0
  exact csv_relation_zero _ relation1077_mem
theorem relation1078_mem : "9,1,529,1;8,1,557,1;0,1,8,1,17,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[21]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1078_zero : nativeImage "9,1,529,1;8,1,557,1;0,1,8,1,17,1,260,1" = 0 := by
  change projection (relationPolynomial "9,1,529,1;8,1,557,1;0,1,8,1,17,1,260,1") = 0
  exact csv_relation_zero _ relation1078_mem
theorem relation1079_mem : "113,1,146,1;112,1,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1079_zero : nativeImage "113,1,146,1;112,1,147,1" = 0 := by
  change projection (relationPolynomial "113,1,146,1;112,1,147,1") = 0
  exact csv_relation_zero _ relation1079_mem
theorem relation1080_mem : "112,1,147,1;72,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[25]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1080_zero : nativeImage "112,1,147,1;72,1,185,1" = 0 := by
  change projection (relationPolynomial "112,1,147,1;72,1,185,1") = 0
  exact csv_relation_zero _ relation1080_mem
theorem relation1081_mem : "72,1,185,1;71,1,188,1;55,1,226,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[28]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1081_zero : nativeImage "72,1,185,1;71,1,188,1;55,1,226,1" = 0 := by
  change projection (relationPolynomial "72,1,185,1;71,1,188,1;55,1,226,1") = 0
  exact csv_relation_zero _ relation1081_mem
theorem relation1082_mem : "71,1,188,1;31,1,299,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[30]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1082_zero : nativeImage "71,1,188,1;31,1,299,1" = 0 := by
  change projection (relationPolynomial "71,1,188,1;31,1,299,1") = 0
  exact csv_relation_zero _ relation1082_mem
theorem relation1083_mem : "55,1,226,1;30,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block1[31]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1083_zero : nativeImage "55,1,226,1;30,1,317,1" = 0 := by
  change projection (relationPolynomial "55,1,226,1;30,1,317,1") = 0
  exact csv_relation_zero _ relation1083_mem
theorem relation1084_mem : "30,1,317,1;30,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block2[0]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1084_zero : nativeImage "30,1,317,1;30,1,316,1" = 0 := by
  change projection (relationPolynomial "30,1,317,1;30,1,316,1") = 0
  exact csv_relation_zero _ relation1084_mem
theorem relation1085_mem : "31,1,299,1;30,1,316,1;8,1,64,1,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block2[2]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1085_zero : nativeImage "31,1,299,1;30,1,316,1;8,1,64,1,138,1" = 0 := by
  change projection (relationPolynomial "31,1,299,1;30,1,316,1;8,1,64,1,138,1") = 0
  exact csv_relation_zero _ relation1085_mem
theorem relation1086_mem : "17,1,432,1;16,1,433,1;15,1,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block5[6]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1086_zero : nativeImage "17,1,432,1;16,1,433,1;15,1,452,1" = 0 := by
  change projection (relationPolynomial "17,1,432,1;16,1,433,1;15,1,452,1") = 0
  exact csv_relation_zero _ relation1086_mem
theorem relation1087_mem : "16,1,433,1;8,1,556,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block5[7]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1087_zero : nativeImage "16,1,433,1;8,1,556,1" = 0 := by
  change projection (relationPolynomial "16,1,433,1;8,1,556,1") = 0
  exact csv_relation_zero _ relation1087_mem
theorem relation1088_mem : "15,1,452,1;2,1,685,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block5[8]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1088_zero : nativeImage "15,1,452,1;2,1,685,1" = 0 := by
  change projection (relationPolynomial "15,1,452,1;2,1,685,1") = 0
  exact csv_relation_zero _ relation1088_mem
theorem relation1089_mem : "2,1,685,1;0,1,722,1;0,40,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block5[9]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1089_zero : nativeImage "2,1,685,1;0,1,722,1;0,40,324,1" = 0 := by
  change projection (relationPolynomial "2,1,685,1;0,1,722,1;0,40,324,1") = 0
  exact csv_relation_zero _ relation1089_mem
theorem relation1090_mem : "17,1,431,1;8,1,554,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block7[12]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1090_zero : nativeImage "17,1,431,1;8,1,554,1" = 0 := by
  change projection (relationPolynomial "17,1,431,1;8,1,554,1") = 0
  exact csv_relation_zero _ relation1090_mem
theorem relation1091_mem : "70,1,198,1;5,1,605,1;3,1,18,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block8[14]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1091_zero : nativeImage "70,1,198,1;5,1,605,1;3,1,18,1,333,1" = 0 := by
  change projection (relationPolynomial "70,1,198,1;5,1,605,1;3,1,18,1,333,1") = 0
  exact csv_relation_zero _ relation1091_mem
theorem relation1092_mem : "5,1,605,1;0,3,720,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block8[16]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1092_zero : nativeImage "5,1,605,1;0,3,720,1" = 0 := by
  change projection (relationPolynomial "5,1,605,1;0,3,720,1") = 0
  exact csv_relation_zero _ relation1092_mem
theorem relation1093_mem : "2,1,713,1;1,1,734,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block9[5]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1093_zero : nativeImage "2,1,713,1;1,1,734,1" = 0 := by
  change projection (relationPolynomial "2,1,713,1;1,1,734,1") = 0
  exact csv_relation_zero _ relation1093_mem
theorem relation1094_mem : "17,1,450,1;10,1,533,1;8,2,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block14[11]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1094_zero : nativeImage "17,1,450,1;10,1,533,1;8,2,373,1" = 0 := by
  change projection (relationPolynomial "17,1,450,1;10,1,533,1;8,2,373,1") = 0
  exact csv_relation_zero _ relation1094_mem
theorem relation1095_mem : "10,1,533,1;8,2,373,1;1,2,708,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block14[12]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1095_zero : nativeImage "10,1,533,1;8,2,373,1;1,2,708,1" = 0 := by
  change projection (relationPolynomial "10,1,533,1;8,2,373,1;1,2,708,1") = 0
  exact csv_relation_zero _ relation1095_mem
theorem relation1096_mem : "73,1,188,1;68,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block14[18]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1096_zero : nativeImage "73,1,188,1;68,1,201,1" = 0 := by
  change projection (relationPolynomial "73,1,188,1;68,1,201,1") = 0
  exact csv_relation_zero _ relation1096_mem
theorem relation1097_mem : "68,1,201,1;22,1,371,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block14[24]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1097_zero : nativeImage "68,1,201,1;22,1,371,1" = 0 := by
  change projection (relationPolynomial "68,1,201,1;22,1,371,1") = 0
  exact csv_relation_zero _ relation1097_mem
theorem relation1098_mem : "17,1,18,1,209,1;16,1,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block14[30]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1098_zero : nativeImage "17,1,18,1,209,1;16,1,450,1" = 0 := by
  change projection (relationPolynomial "17,1,18,1,209,1;16,1,450,1") = 0
  exact csv_relation_zero _ relation1098_mem
theorem relation1099_mem : "16,1,450,1;8,2,69,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block15[2]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1099_zero : nativeImage "16,1,450,1;8,2,69,1,80,1" = 0 := by
  change projection (relationPolynomial "16,1,450,1;8,2,69,1,80,1") = 0
  exact csv_relation_zero _ relation1099_mem
theorem relation1100_mem : "73,1,187,1;67,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block15[8]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1100_zero : nativeImage "73,1,187,1;67,1,201,1" = 0 := by
  change projection (relationPolynomial "73,1,187,1;67,1,201,1") = 0
  exact csv_relation_zero _ relation1100_mem
theorem relation1101_mem : "67,1,201,1;48,1,250,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block15[11]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1101_zero : nativeImage "67,1,201,1;48,1,250,1" = 0 := by
  change projection (relationPolynomial "67,1,201,1;48,1,250,1") = 0
  exact csv_relation_zero _ relation1101_mem
theorem relation1102_mem : "2,2,656,1;1,1,3,1,639,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block16[25]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1102_zero : nativeImage "2,2,656,1;1,1,3,1,639,1" = 0 := by
  change projection (relationPolynomial "2,2,656,1;1,1,3,1,639,1") = 0
  exact csv_relation_zero _ relation1102_mem
theorem relation1103_mem : "17,1,449,1;8,1,568,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block18[1]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1103_zero : nativeImage "17,1,449,1;8,1,568,1" = 0 := by
  change projection (relationPolynomial "17,1,449,1;8,1,568,1") = 0
  exact csv_relation_zero _ relation1103_mem
theorem relation1104_mem : "8,1,568,1;3,1,655,1;2,1,703,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block18[6]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1104_zero : nativeImage "8,1,568,1;3,1,655,1;2,1,703,1" = 0 := by
  change projection (relationPolynomial "8,1,568,1;3,1,655,1;2,1,703,1") = 0
  exact csv_relation_zero _ relation1104_mem
theorem relation1105_mem : "3,1,655,1;1,1,728,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block18[8]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1105_zero : nativeImage "3,1,655,1;1,1,728,1" = 0 := by
  change projection (relationPolynomial "3,1,655,1;1,1,728,1") = 0
  exact csv_relation_zero _ relation1105_mem
theorem relation1106_mem : "2,1,703,1;0,1,739,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block18[9]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1106_zero : nativeImage "2,1,703,1;0,1,739,1" = 0 := by
  change projection (relationPolynomial "2,1,703,1;0,1,739,1") = 0
  exact csv_relation_zero _ relation1106_mem
theorem relation1107_mem : "17,1,448,1;16,1,449,1;15,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block19[3]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1107_zero : nativeImage "17,1,448,1;16,1,449,1;15,1,475,1" = 0 := by
  change projection (relationPolynomial "17,1,448,1;16,1,449,1;15,1,475,1") = 0
  exact csv_relation_zero _ relation1107_mem
theorem relation1108_mem : "16,1,449,1;15,1,475,1;8,1,69,1,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block19[6]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1108_zero : nativeImage "16,1,449,1;15,1,475,1;8,1,69,1,138,1" = 0 := by
  change projection (relationPolynomial "16,1,449,1;15,1,475,1;8,1,69,1,138,1") = 0
  exact csv_relation_zero _ relation1108_mem
theorem relation1109_mem : "0,1,72,1,188,1;0,5,693,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block19[12]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1109_zero : nativeImage "0,1,72,1,188,1;0,5,693,1" = 0 := by
  change projection (relationPolynomial "0,1,72,1,188,1;0,5,693,1") = 0
  exact csv_relation_zero _ relation1109_mem
theorem relation1110_mem : "3,1,18,1,341,1;1,1,750,1" ∈ LinE2.RawData.relations := by
  exact relation_member 25 chunkBound rows transcription
    (block28[25]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1110_zero : nativeImage "3,1,18,1,341,1;1,1,750,1" = 0 := by
  change projection (relationPolynomial "3,1,18,1,341,1;1,1,750,1") = 0
  exact csv_relation_zero _ relation1110_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk025
