module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk028
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[28]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 28 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[28]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation1173_mem : "8,1,18,1,278,1;4,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block0[1]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1173_zero : nativeImage "8,1,18,1,278,1;4,1,655,1" = 0 := by
  change projection (relationPolynomial "8,1,18,1,278,1;4,1,655,1") = 0
  exact csv_relation_zero _ relation1173_mem
theorem relation1174_mem : "109,1,163,1;7,2,480,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block10[3]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1174_zero : nativeImage "109,1,163,1;7,2,480,1" = 0 := by
  change projection (relationPolynomial "109,1,163,1;7,2,480,1") = 0
  exact csv_relation_zero _ relation1174_mem
theorem relation1175_mem : "7,2,480,1;3,1,18,1,376,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block10[4]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1175_zero : nativeImage "7,2,480,1;3,1,18,1,376,1" = 0 := by
  change projection (relationPolynomial "7,2,480,1;3,1,18,1,376,1") = 0
  exact csv_relation_zero _ relation1175_mem
theorem relation1176_mem : "3,1,18,1,376,1;1,1,782,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block10[5]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1176_zero : nativeImage "3,1,18,1,376,1;1,1,782,1" = 0 := by
  change projection (relationPolynomial "3,1,18,1,376,1;1,1,782,1") = 0
  exact csv_relation_zero _ relation1176_mem
theorem relation1177_mem : "3,1,713,1;0,1,790,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block11[5]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1177_zero : nativeImage "3,1,713,1;0,1,790,1" = 0 := by
  change projection (relationPolynomial "3,1,713,1;0,1,790,1") = 0
  exact csv_relation_zero _ relation1177_mem
theorem relation1178_mem : "3,1,710,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block13[20]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1178_zero : nativeImage "3,1,710,1" = 0 := by
  change projection (relationPolynomial "3,1,710,1") = 0
  exact csv_relation_zero _ relation1178_mem
theorem relation1179_mem : "2,1,76,1,189,1;1,1,3,1,680,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block14[19]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1179_zero : nativeImage "2,1,76,1,189,1;1,1,3,1,680,1" = 0 := by
  change projection (relationPolynomial "2,1,76,1,189,1;1,1,3,1,680,1") = 0
  exact csv_relation_zero _ relation1179_mem
theorem relation1180_mem : "23,1,423,1;13,2,294,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block20[9]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1180_zero : nativeImage "23,1,423,1;13,2,294,1" = 0 := by
  change projection (relationPolynomial "23,1,423,1;13,2,294,1") = 0
  exact csv_relation_zero _ relation1180_mem
theorem relation1181_mem : "22,1,423,1;8,1,13,2,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block21[14]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1181_zero : nativeImage "22,1,423,1;8,1,13,2,209,1" = 0 := by
  change projection (relationPolynomial "22,1,423,1;8,1,13,2,209,1") = 0
  exact csv_relation_zero _ relation1181_mem
theorem relation1182_mem : "32,1,346,1;13,2,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block24[2]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1182_zero : nativeImage "32,1,346,1;13,2,292,1" = 0 := by
  change projection (relationPolynomial "32,1,346,1;13,2,292,1") = 0
  exact csv_relation_zero _ relation1182_mem
theorem relation1183_mem : "42,1,292,1;8,1,13,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block24[26]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1183_zero : nativeImage "42,1,292,1;8,1,13,1,346,1" = 0 := by
  change projection (relationPolynomial "42,1,292,1;8,1,13,1,346,1") = 0
  exact csv_relation_zero _ relation1183_mem
theorem relation1184_mem : "46,1,278,1;42,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[7]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1184_zero : nativeImage "46,1,278,1;42,1,291,1" = 0 := by
  change projection (relationPolynomial "46,1,278,1;42,1,291,1") = 0
  exact csv_relation_zero _ relation1184_mem
theorem relation1185_mem : "17,1,492,1;13,1,549,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[17]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1185_zero : nativeImage "17,1,492,1;13,1,549,1" = 0 := by
  change projection (relationPolynomial "17,1,492,1;13,1,549,1") = 0
  exact csv_relation_zero _ relation1185_mem
theorem relation1186_mem : "13,1,549,1;9,1,574,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[18]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1186_zero : nativeImage "13,1,549,1;9,1,574,1" = 0 := by
  change projection (relationPolynomial "13,1,549,1;9,1,574,1") = 0
  exact csv_relation_zero _ relation1186_mem
theorem relation1187_mem : "42,1,291,1;8,1,602,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[19]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1187_zero : nativeImage "42,1,291,1;8,1,602,1" = 0 := by
  change projection (relationPolynomial "42,1,291,1;8,1,602,1") = 0
  exact csv_relation_zero _ relation1187_mem
theorem relation1188_mem : "9,1,574,1;8,2,420,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[22]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1188_zero : nativeImage "9,1,574,1;8,2,420,1" = 0 := by
  change projection (relationPolynomial "9,1,574,1;8,2,420,1") = 0
  exact csv_relation_zero _ relation1188_mem
theorem relation1189_mem : "64,1,218,1;49,1,261,1;45,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block25[29]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1189_zero : nativeImage "64,1,218,1;49,1,261,1;45,1,278,1" = 0 := by
  change projection (relationPolynomial "64,1,218,1;49,1,261,1;45,1,278,1") = 0
  exact csv_relation_zero _ relation1189_mem
theorem relation1190_mem : "49,1,261,1;39,1,318,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[0]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1190_zero : nativeImage "49,1,261,1;39,1,318,1" = 0 := by
  change projection (relationPolynomial "49,1,261,1;39,1,318,1") = 0
  exact csv_relation_zero _ relation1190_mem
theorem relation1191_mem : "39,1,318,1;31,1,348,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[1]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1191_zero : nativeImage "39,1,318,1;31,1,348,1" = 0 := by
  change projection (relationPolynomial "39,1,318,1;31,1,348,1") = 0
  exact csv_relation_zero _ relation1191_mem
theorem relation1192_mem : "45,1,278,1;20,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[4]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1192_zero : nativeImage "45,1,278,1;20,1,454,1" = 0 := by
  change projection (relationPolynomial "45,1,278,1;20,1,454,1") = 0
  exact csv_relation_zero _ relation1192_mem
theorem relation1193_mem : "31,1,348,1;19,1,455,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[5]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1193_zero : nativeImage "31,1,348,1;19,1,455,1" = 0 := by
  change projection (relationPolynomial "31,1,348,1;19,1,455,1") = 0
  exact csv_relation_zero _ relation1193_mem
theorem relation1194_mem : "19,1,455,1;16,1,492,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[6]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1194_zero : nativeImage "19,1,455,1;16,1,492,1" = 0 := by
  change projection (relationPolynomial "19,1,455,1;16,1,492,1") = 0
  exact csv_relation_zero _ relation1194_mem
theorem relation1195_mem : "16,1,492,1;9,1,573,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[7]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1195_zero : nativeImage "16,1,492,1;9,1,573,1" = 0 := by
  change projection (relationPolynomial "16,1,492,1;9,1,573,1") = 0
  exact csv_relation_zero _ relation1195_mem
theorem relation1196_mem : "9,1,573,1;8,1,599,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[8]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1196_zero : nativeImage "9,1,573,1;8,1,599,1" = 0 := by
  change projection (relationPolynomial "9,1,573,1;8,1,599,1") = 0
  exact csv_relation_zero _ relation1196_mem
theorem relation1197_mem : "20,1,454,1;8,1,17,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[9]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1197_zero : nativeImage "20,1,454,1;8,1,17,1,292,1" = 0 := by
  change projection (relationPolynomial "20,1,454,1;8,1,17,1,292,1") = 0
  exact csv_relation_zero _ relation1197_mem
theorem relation1198_mem : "113,1,160,1;19,1,454,1;8,1,598,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[28]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1198_zero : nativeImage "113,1,160,1;19,1,454,1;8,1,598,1" = 0 := by
  change projection (relationPolynomial "113,1,160,1;19,1,454,1;8,1,598,1") = 0
  exact csv_relation_zero _ relation1198_mem
theorem relation1199_mem : "19,1,454,1;8,1,16,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block26[29]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1199_zero : nativeImage "19,1,454,1;8,1,16,1,292,1" = 0 := by
  change projection (relationPolynomial "19,1,454,1;8,1,16,1,292,1") = 0
  exact csv_relation_zero _ relation1199_mem
theorem relation1200_mem : "39,1,316,1;31,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block27[14]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1200_zero : nativeImage "39,1,316,1;31,1,346,1" = 0 := by
  change projection (relationPolynomial "39,1,316,1;31,1,346,1") = 0
  exact csv_relation_zero _ relation1200_mem
theorem relation1201_mem : "31,1,347,1;31,1,346,1;8,1,64,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block27[16]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1201_zero : nativeImage "31,1,347,1;31,1,346,1;8,1,64,1,149,1" = 0 := by
  change projection (relationPolynomial "31,1,347,1;31,1,346,1;8,1,64,1,149,1") = 0
  exact csv_relation_zero _ relation1201_mem
theorem relation1202_mem : "31,1,346,1;8,3,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block27[18]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1202_zero : nativeImage "31,1,346,1;8,3,260,1" = 0 := by
  change projection (relationPolynomial "31,1,346,1;8,3,260,1") = 0
  exact csv_relation_zero _ relation1202_mem
theorem relation1203_mem : "17,1,490,1;8,3,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block29[31]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1203_zero : nativeImage "17,1,490,1;8,3,257,1" = 0 := by
  change projection (relationPolynomial "17,1,490,1;8,3,257,1") = 0
  exact csv_relation_zero _ relation1203_mem
theorem relation1204_mem : "17,1,489,1;9,1,572,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block30[15]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1204_zero : nativeImage "17,1,489,1;9,1,572,1" = 0 := by
  change projection (relationPolynomial "17,1,489,1;9,1,572,1") = 0
  exact csv_relation_zero _ relation1204_mem
theorem relation1205_mem : "9,1,572,1;8,1,597,1;0,3,759,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block30[17]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1205_zero : nativeImage "9,1,572,1;8,1,597,1;0,3,759,1" = 0 := by
  change projection (relationPolynomial "9,1,572,1;8,1,597,1;0,3,759,1") = 0
  exact csv_relation_zero _ relation1205_mem
theorem relation1206_mem : "49,1,258,1;31,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block30[23]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1206_zero : nativeImage "49,1,258,1;31,1,344,1" = 0 := by
  change projection (relationPolynomial "49,1,258,1;31,1,344,1") = 0
  exact csv_relation_zero _ relation1206_mem
theorem relation1207_mem : "31,1,344,1;16,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block30[24]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1207_zero : nativeImage "31,1,344,1;16,1,489,1" = 0 := by
  change projection (relationPolynomial "31,1,344,1;16,1,489,1") = 0
  exact csv_relation_zero _ relation1207_mem
theorem relation1208_mem : "16,1,489,1;8,1,596,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block30[25]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1208_zero : nativeImage "16,1,489,1;8,1,596,1" = 0 := by
  change projection (relationPolynomial "16,1,489,1;8,1,596,1") = 0
  exact csv_relation_zero _ relation1208_mem
theorem relation1209_mem : "110,1,160,1;71,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block31[4]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1209_zero : nativeImage "110,1,160,1;71,1,206,1" = 0 := by
  change projection (relationPolynomial "110,1,160,1;71,1,206,1") = 0
  exact csv_relation_zero _ relation1209_mem
theorem relation1210_mem : "71,1,206,1;49,1,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block31[6]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1210_zero : nativeImage "71,1,206,1;49,1,257,1" = 0 := by
  change projection (relationPolynomial "71,1,206,1;49,1,257,1") = 0
  exact csv_relation_zero _ relation1210_mem
theorem relation1211_mem : "49,1,257,1;31,1,343,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block31[8]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1211_zero : nativeImage "49,1,257,1;31,1,343,1" = 0 := by
  change projection (relationPolynomial "49,1,257,1;31,1,343,1") = 0
  exact csv_relation_zero _ relation1211_mem
theorem relation1212_mem : "31,1,343,1;28,1,402,1;19,1,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block31[10]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1212_zero : nativeImage "31,1,343,1;28,1,402,1;19,1,452,1" = 0 := by
  change projection (relationPolynomial "31,1,343,1;28,1,402,1;19,1,452,1") = 0
  exact csv_relation_zero _ relation1212_mem
theorem relation1213_mem : "19,1,452,1;8,1,595,1;1,1,59,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 28 chunkBound rows transcription
    (block31[13]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1213_zero : nativeImage "19,1,452,1;8,1,595,1;1,1,59,1,224,1" = 0 := by
  change projection (relationPolynomial "19,1,452,1;8,1,595,1;1,1,59,1,224,1") = 0
  exact csv_relation_zero _ relation1213_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk028
