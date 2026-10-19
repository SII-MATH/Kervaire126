module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk031
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[31]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 31 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[31]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
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
theorem relation1298_mem : "0,2,3,1,717,1;0,6,762,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block7[19]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1298_zero : nativeImage "0,2,3,1,717,1;0,6,762,1" = 0 := by
  change projection (relationPolynomial "0,2,3,1,717,1;0,6,762,1") = 0
  exact csv_relation_zero _ relation1298_mem
theorem relation1299_mem : "46,1,292,1;9,1,13,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block10[17]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1299_zero : nativeImage "46,1,292,1;9,1,13,1,346,1" = 0 := by
  change projection (relationPolynomial "46,1,292,1;9,1,13,1,346,1") = 0
  exact csv_relation_zero _ relation1299_mem
theorem relation1300_mem : "42,1,316,1;23,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block11[27]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1300_zero : nativeImage "42,1,316,1;23,1,454,1" = 0 := by
  change projection (relationPolynomial "42,1,316,1;23,1,454,1") = 0
  exact csv_relation_zero _ relation1300_mem
theorem relation1301_mem : "23,1,454,1;14,1,560,1;9,1,602,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[2]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1301_zero : nativeImage "23,1,454,1;14,1,560,1;9,1,602,1" = 0 := by
  change projection (relationPolynomial "23,1,454,1;14,1,560,1;9,1,602,1") = 0
  exact csv_relation_zero _ relation1301_mem
theorem relation1302_mem : "14,1,560,1;9,1,600,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[4]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1302_zero : nativeImage "14,1,560,1;9,1,600,1" = 0 := by
  change projection (relationPolynomial "14,1,560,1;9,1,600,1") = 0
  exact csv_relation_zero _ relation1302_mem
theorem relation1303_mem : "9,1,602,1;8,1,625,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[5]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1303_zero : nativeImage "9,1,602,1;8,1,625,1" = 0 := by
  change projection (relationPolynomial "9,1,602,1;8,1,625,1") = 0
  exact csv_relation_zero _ relation1303_mem
theorem relation1304_mem : "9,1,600,1;6,1,643,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[7]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1304_zero : nativeImage "9,1,600,1;6,1,643,1" = 0 := by
  change projection (relationPolynomial "9,1,600,1;6,1,643,1") = 0
  exact csv_relation_zero _ relation1304_mem
theorem relation1305_mem : "6,1,643,1;0,2,810,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[9]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1305_zero : nativeImage "6,1,643,1;0,2,810,1" = 0 := by
  change projection (relationPolynomial "6,1,643,1;0,2,810,1") = 0
  exact csv_relation_zero _ relation1305_mem
theorem relation1306_mem : "0,2,810,1;0,3,797,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[10]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1306_zero : nativeImage "0,2,810,1;0,3,797,1" = 0 := by
  change projection (relationPolynomial "0,2,810,1;0,3,797,1") = 0
  exact csv_relation_zero _ relation1306_mem
theorem relation1307_mem : "17,1,518,1;13,1,573,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block12[31]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1307_zero : nativeImage "17,1,518,1;13,1,573,1" = 0 := by
  change projection (relationPolynomial "17,1,518,1;13,1,573,1") = 0
  exact csv_relation_zero _ relation1307_mem
theorem relation1308_mem : "13,1,573,1;9,1,599,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block13[0]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1308_zero : nativeImage "13,1,573,1;9,1,599,1" = 0 := by
  change projection (relationPolynomial "13,1,573,1;9,1,599,1") = 0
  exact csv_relation_zero _ relation1308_mem
theorem relation1309_mem : "9,1,599,1;8,2,455,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block13[2]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1309_zero : nativeImage "9,1,599,1;8,2,455,1" = 0 := by
  change projection (relationPolynomial "9,1,599,1;8,2,455,1") = 0
  exact csv_relation_zero _ relation1309_mem
theorem relation1310_mem : "17,1,517,1;16,1,518,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block13[24]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1310_zero : nativeImage "17,1,517,1;16,1,518,1" = 0 := by
  change projection (relationPolynomial "17,1,517,1;16,1,518,1") = 0
  exact csv_relation_zero _ relation1310_mem
theorem relation1311_mem : "16,1,518,1;9,1,598,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block13[26]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1311_zero : nativeImage "16,1,518,1;9,1,598,1" = 0 := by
  change projection (relationPolynomial "16,1,518,1;9,1,598,1") = 0
  exact csv_relation_zero _ relation1311_mem
theorem relation1312_mem : "9,1,598,1;8,1,624,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block13[27]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1312_zero : nativeImage "9,1,598,1;8,1,624,1" = 0 := by
  change projection (relationPolynomial "9,1,598,1;8,1,624,1") = 0
  exact csv_relation_zero _ relation1312_mem
theorem relation1313_mem : "17,2,244,1;8,1,31,1,245,1;0,2,64,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block18[3]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1313_zero : nativeImage "17,2,244,1;8,1,31,1,245,1;0,2,64,1,224,1" = 0 := by
  change projection (relationPolynomial "17,2,244,1;8,1,31,1,245,1;0,2,64,1,224,1") = 0
  exact csv_relation_zero _ relation1313_mem
theorem relation1314_mem : "43,1,332,1;35,1,413,1;35,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block24[21]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1314_zero : nativeImage "43,1,332,1;35,1,413,1;35,1,412,1" = 0 := by
  change projection (relationPolynomial "43,1,332,1;35,1,413,1;35,1,412,1") = 0
  exact csv_relation_zero _ relation1314_mem
theorem relation1315_mem : "35,1,412,1;3,1,76,1,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block25[2]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1315_zero : nativeImage "35,1,412,1;3,1,76,1,190,1" = 0 := by
  change projection (relationPolynomial "35,1,412,1;3,1,76,1,190,1") = 0
  exact csv_relation_zero _ relation1315_mem
theorem relation1316_mem : "35,1,413,1;1,1,3,1,732,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block25[4]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1316_zero : nativeImage "35,1,413,1;1,1,3,1,732,1" = 0 := by
  change projection (relationPolynomial "35,1,413,1;1,1,3,1,732,1") = 0
  exact csv_relation_zero _ relation1316_mem
theorem relation1317_mem : "20,1,504,1;8,1,9,1,445,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block27[10]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1317_zero : nativeImage "20,1,504,1;8,1,9,1,445,1" = 0 := by
  change projection (relationPolynomial "20,1,504,1;8,1,9,1,445,1") = 0
  exact csv_relation_zero _ relation1317_mem
theorem relation1318_mem : "107,1,181,1;3,1,76,1,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block27[11]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1318_zero : nativeImage "107,1,181,1;3,1,76,1,189,1" = 0 := by
  change projection (relationPolynomial "107,1,181,1;3,1,76,1,189,1") = 0
  exact csv_relation_zero _ relation1318_mem
theorem relation1319_mem : "8,1,9,1,445,1;3,1,76,1,189,1;1,1,825,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block27[13]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1319_zero : nativeImage "8,1,9,1,445,1;3,1,76,1,189,1;1,1,825,1" = 0 := by
  change projection (relationPolynomial "8,1,9,1,445,1;3,1,76,1,189,1;1,1,825,1") = 0
  exact csv_relation_zero _ relation1319_mem
theorem relation1320_mem : "23,1,476,1;13,2,332,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block29[24]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1320_zero : nativeImage "23,1,476,1;13,2,332,1" = 0 := by
  change projection (relationPolynomial "23,1,476,1;13,2,332,1") = 0
  exact csv_relation_zero _ relation1320_mem
theorem relation1321_mem : "23,1,474,1;13,2,331,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block30[25]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1321_zero : nativeImage "23,1,474,1;13,2,331,1" = 0 := by
  change projection (relationPolynomial "23,1,474,1;13,2,331,1") = 0
  exact csv_relation_zero _ relation1321_mem
theorem relation1322_mem : "39,1,367,1;31,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block31[25]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1322_zero : nativeImage "39,1,367,1;31,1,415,1" = 0 := by
  change projection (relationPolynomial "39,1,367,1;31,1,415,1") = 0
  exact csv_relation_zero _ relation1322_mem
theorem relation1323_mem : "31,1,415,1;22,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block31[29]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1323_zero : nativeImage "31,1,415,1;22,1,475,1" = 0 := by
  change projection (relationPolynomial "31,1,415,1;22,1,475,1") = 0
  exact csv_relation_zero _ relation1323_mem
theorem relation1324_mem : "22,1,475,1;20,1,502,1" ∈ LinE2.RawData.relations := by
  exact relation_member 31 chunkBound rows transcription
    (block31[31]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1324_zero : nativeImage "22,1,475,1;20,1,502,1" = 0 := by
  change projection (relationPolynomial "22,1,475,1;20,1,502,1") = 0
  exact csv_relation_zero _ relation1324_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk031
