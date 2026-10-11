module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk030
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
open Lean Elab Tactic in
private def block0 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[30]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 30 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[30]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block22_mem : block22 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 22) (by decide)
private theorem block22_in_rows (r : List Char) (hr : r ∈ block22) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block22, block22_mem, hr⟩
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
theorem relation1265_mem : "37,1,352,1;3,1,735,1;0,2,18,1,479,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block0[22]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1265_zero : nativeImage "37,1,352,1;3,1,735,1;0,2,18,1,479,1" = 0 := by
  change projection (relationPolynomial "37,1,352,1;3,1,735,1;0,2,18,1,479,1") = 0
  exact csv_relation_zero _ relation1265_mem
theorem relation1266_mem : "0,2,18,1,479,1;0,5,18,1,446,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block0[23]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1266_zero : nativeImage "0,2,18,1,479,1;0,5,18,1,446,1" = 0 := by
  change projection (relationPolynomial "0,2,18,1,479,1;0,5,18,1,446,1") = 0
  exact csv_relation_zero _ relation1266_mem
theorem relation1267_mem : "36,1,352,1;3,1,731,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block2[4]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1267_zero : nativeImage "36,1,352,1;3,1,731,1" = 0 := by
  change projection (relationPolynomial "36,1,352,1;3,1,731,1") = 0
  exact csv_relation_zero _ relation1267_mem
theorem relation1268_mem : "24,1,450,1;13,1,570,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block2[24]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1268_zero : nativeImage "24,1,450,1;13,1,570,1" = 0 := by
  change projection (relationPolynomial "24,1,450,1;13,1,570,1") = 0
  exact csv_relation_zero _ relation1268_mem
theorem relation1269_mem : "23,1,450,1;13,1,569,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block3[21]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1269_zero : nativeImage "23,1,450,1;13,1,569,1" = 0 := by
  change projection (relationPolynomial "23,1,450,1;13,1,569,1") = 0
  exact csv_relation_zero _ relation1269_mem
theorem relation1270_mem : "0,1,8,2,443,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block5[31]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1270_zero : nativeImage "0,1,8,2,443,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,443,1") = 0
  exact csv_relation_zero _ relation1270_mem
theorem relation1271_mem : "73,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block6[10]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1271_zero : nativeImage "73,1,212,1" = 0 := by
  change projection (relationPolynomial "73,1,212,1") = 0
  exact csv_relation_zero _ relation1271_mem
theorem relation1272_mem : "8,1,17,1,314,1;7,1,638,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block8[5]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1272_zero : nativeImage "8,1,17,1,314,1;7,1,638,1" = 0 := by
  change projection (relationPolynomial "8,1,17,1,314,1;7,1,638,1") = 0
  exact csv_relation_zero _ relation1272_mem
theorem relation1273_mem : "7,1,638,1;4,1,692,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block8[7]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1273_zero : nativeImage "7,1,638,1;4,1,692,1" = 0 := by
  change projection (relationPolynomial "7,1,638,1;4,1,692,1") = 0
  exact csv_relation_zero _ relation1273_mem
theorem relation1274_mem : "4,1,692,1;1,1,798,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block8[11]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1274_zero : nativeImage "4,1,692,1;1,1,798,1" = 0 := by
  change projection (relationPolynomial "4,1,692,1;1,1,798,1") = 0
  exact csv_relation_zero _ relation1274_mem
theorem relation1275_mem : "8,2,449,1;0,1,80,1,201,1;0,1,3,1,717,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block10[19]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1275_zero : nativeImage "8,2,449,1;0,1,80,1,201,1;0,1,3,1,717,1" = 0 := by
  change projection (relationPolynomial "8,2,449,1;0,1,80,1,201,1;0,1,3,1,717,1") = 0
  exact csv_relation_zero _ relation1275_mem
theorem relation1276_mem : "0,1,80,1,201,1;0,5,762,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block10[20]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1276_zero : nativeImage "0,1,80,1,201,1;0,5,762,1" = 0 := by
  change projection (relationPolynomial "0,1,80,1,201,1;0,5,762,1") = 0
  exact csv_relation_zero _ relation1276_mem
theorem relation1277_mem : "66,1,226,1;59,1,243,1;48,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[19]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1277_zero : nativeImage "66,1,226,1;59,1,243,1;48,1,278,1" = 0 := by
  change projection (relationPolynomial "66,1,226,1;59,1,243,1;48,1,278,1") = 0
  exact csv_relation_zero _ relation1277_mem
theorem relation1278_mem : "59,1,243,1;28,1,420,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[22]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1278_zero : nativeImage "59,1,243,1;28,1,420,1" = 0 := by
  change projection (relationPolynomial "59,1,243,1;28,1,420,1") = 0
  exact csv_relation_zero _ relation1278_mem
theorem relation1279_mem : "28,1,420,1;27,1,426,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[23]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1279_zero : nativeImage "28,1,420,1;27,1,426,1" = 0 := by
  change projection (relationPolynomial "28,1,420,1;27,1,426,1") = 0
  exact csv_relation_zero _ relation1279_mem
theorem relation1280_mem : "27,1,426,1;14,1,552,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[28]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1280_zero : nativeImage "27,1,426,1;14,1,552,1" = 0 := by
  change projection (relationPolynomial "27,1,426,1;14,1,552,1") = 0
  exact csv_relation_zero _ relation1280_mem
theorem relation1281_mem : "14,1,552,1;9,1,586,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[29]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1281_zero : nativeImage "14,1,552,1;9,1,586,1" = 0 := by
  change projection (relationPolynomial "14,1,552,1;9,1,586,1") = 0
  exact csv_relation_zero _ relation1281_mem
theorem relation1282_mem : "48,1,278,1;9,1,586,1;5,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block12[30]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1282_zero : nativeImage "48,1,278,1;9,1,586,1;5,1,655,1" = 0 := by
  change projection (relationPolynomial "48,1,278,1;9,1,586,1;5,1,655,1") = 0
  exact csv_relation_zero _ relation1282_mem
theorem relation1283_mem : "5,1,655,1;1,1,797,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block13[0]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1283_zero : nativeImage "5,1,655,1;1,1,797,1" = 0 := by
  change projection (relationPolynomial "5,1,655,1;1,1,797,1") = 0
  exact csv_relation_zero _ relation1283_mem
theorem relation1284_mem : "0,1,808,1;0,1,807,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block17[7]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1284_zero : nativeImage "0,1,808,1;0,1,807,1" = 0 := by
  change projection (relationPolynomial "0,1,808,1;0,1,807,1") = 0
  exact csv_relation_zero _ relation1284_mem
theorem relation1285_mem : "7,2,507,1;3,1,749,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block21[12]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1285_zero : nativeImage "7,2,507,1;3,1,749,1" = 0 := by
  change projection (relationPolynomial "7,2,507,1;3,1,749,1") = 0
  exact csv_relation_zero _ relation1285_mem
theorem relation1286_mem : "38,1,367,1;7,1,68,1,163,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[10]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1286_zero : nativeImage "38,1,367,1;7,1,68,1,163,1" = 0 := by
  change projection (relationPolynomial "38,1,367,1;7,1,68,1,163,1") = 0
  exact csv_relation_zero _ relation1286_mem
theorem relation1287_mem : "93,1,198,1;37,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[24]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1287_zero : nativeImage "93,1,198,1;37,1,367,1" = 0 := by
  change projection (relationPolynomial "93,1,198,1;37,1,367,1") = 0
  exact csv_relation_zero _ relation1287_mem
theorem relation1288_mem : "37,1,367,1;36,1,368,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[25]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1288_zero : nativeImage "37,1,367,1;36,1,368,1" = 0 := by
  change projection (relationPolynomial "37,1,367,1;36,1,368,1") = 0
  exact csv_relation_zero _ relation1288_mem
theorem relation1289_mem : "36,1,368,1;35,1,395,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[26]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1289_zero : nativeImage "36,1,368,1;35,1,395,1" = 0 := by
  change projection (relationPolynomial "36,1,368,1;35,1,395,1") = 0
  exact csv_relation_zero _ relation1289_mem
theorem relation1290_mem : "35,1,395,1;35,1,394,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[27]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1290_zero : nativeImage "35,1,395,1;35,1,394,1" = 0 := by
  change projection (relationPolynomial "35,1,395,1;35,1,394,1") = 0
  exact csv_relation_zero _ relation1290_mem
theorem relation1291_mem : "35,1,394,1;35,1,392,1;34,1,396,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block22[31]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1291_zero : nativeImage "35,1,394,1;35,1,392,1;34,1,396,1" = 0 := by
  change projection (relationPolynomial "35,1,394,1;35,1,392,1;34,1,396,1") = 0
  exact csv_relation_zero _ relation1291_mem
theorem relation1292_mem : "35,1,392,1;34,1,396,1;3,1,744,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block23[14]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1292_zero : nativeImage "35,1,392,1;34,1,396,1;3,1,744,1" = 0 := by
  change projection (relationPolynomial "35,1,392,1;34,1,396,1;3,1,744,1") = 0
  exact csv_relation_zero _ relation1292_mem
theorem relation1293_mem : "3,1,744,1;2,2,746,1;1,1,7,1,632,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block23[19]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1293_zero : nativeImage "3,1,744,1;2,2,746,1;1,1,7,1,632,1" = 0 := by
  change projection (relationPolynomial "3,1,744,1;2,2,746,1;1,1,7,1,632,1") = 0
  exact csv_relation_zero _ relation1293_mem
theorem relation1294_mem : "2,2,746,1;1,2,792,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block23[20]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1294_zero : nativeImage "2,2,746,1;1,2,792,1" = 0 := by
  change projection (relationPolynomial "2,2,746,1;1,2,792,1") = 0
  exact csv_relation_zero _ relation1294_mem
theorem relation1295_mem : "1,2,792,1;0,2,818,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block23[22]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1295_zero : nativeImage "1,2,792,1;0,2,818,1" = 0 := by
  change projection (relationPolynomial "1,2,792,1;0,2,818,1") = 0
  exact csv_relation_zero _ relation1295_mem
theorem relation1296_mem : "2,1,788,1;1,1,3,1,719,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block24[28]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1296_zero : nativeImage "2,1,788,1;1,1,3,1,719,1" = 0 := by
  change projection (relationPolynomial "2,1,788,1;1,1,3,1,719,1") = 0
  exact csv_relation_zero _ relation1296_mem
theorem relation1297_mem : "13,1,575,1" ∈ LinE2.RawData.relations := by
  exact relation_member 30 chunkBound rows transcription
    (block29[2]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1297_zero : nativeImage "13,1,575,1" = 0 := by
  change projection (relationPolynomial "13,1,575,1") = 0
  exact csv_relation_zero _ relation1297_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk030
