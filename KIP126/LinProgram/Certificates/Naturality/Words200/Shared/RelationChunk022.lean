module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk022
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[22]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 22 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[22]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
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
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block19_mem : block19 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 19) (by decide)
private theorem block19_in_rows (r : List Char) (hr : r ∈ block19) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block19, block19_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
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
theorem relation968_mem : "68,1,176,1;36,1,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block3[26]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation968_zero : nativeImage "68,1,176,1;36,1,267,1" = 0 := by
  change projection (relationPolynomial "68,1,176,1;36,1,267,1") = 0
  exact csv_relation_zero _ relation968_mem
theorem relation969_mem : "36,1,267,1;3,1,609,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block4[7]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation969_zero : nativeImage "36,1,267,1;3,1,609,1" = 0 := by
  change projection (relationPolynomial "36,1,267,1;3,1,609,1") = 0
  exact csv_relation_zero _ relation969_mem
theorem relation970_mem : "17,1,384,1;8,2,9,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block6[4]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation970_zero : nativeImage "17,1,384,1;8,2,9,1,209,1" = 0 := by
  change projection (relationPolynomial "17,1,384,1;8,2,9,1,209,1") = 0
  exact csv_relation_zero _ relation970_mem
theorem relation971_mem : "29,1,292,1;23,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block7[21]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation971_zero : nativeImage "29,1,292,1;23,1,316,1" = 0 := by
  change projection (relationPolynomial "29,1,292,1;23,1,316,1") = 0
  exact csv_relation_zero _ relation971_mem
theorem relation972_mem : "17,1,383,1;13,1,455,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block7[26]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation972_zero : nativeImage "17,1,383,1;13,1,455,1" = 0 := by
  change projection (relationPolynomial "17,1,383,1;13,1,455,1") = 0
  exact csv_relation_zero _ relation972_mem
theorem relation973_mem : "13,1,455,1;9,1,492,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block7[28]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation973_zero : nativeImage "13,1,455,1;9,1,492,1" = 0 := by
  change projection (relationPolynomial "13,1,455,1;9,1,492,1") = 0
  exact csv_relation_zero _ relation973_mem
theorem relation974_mem : "9,1,492,1;8,2,318,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block7[29]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation974_zero : nativeImage "9,1,492,1;8,2,318,1" = 0 := by
  change projection (relationPolynomial "9,1,492,1;8,2,318,1") = 0
  exact csv_relation_zero _ relation974_mem
theorem relation975_mem : "20,1,346,1;13,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block8[19]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation975_zero : nativeImage "20,1,346,1;13,1,454,1" = 0 := by
  change projection (relationPolynomial "20,1,346,1;13,1,454,1") = 0
  exact csv_relation_zero _ relation975_mem
theorem relation976_mem : "13,1,454,1;8,1,9,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block8[22]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation976_zero : nativeImage "13,1,454,1;8,1,9,1,292,1" = 0 := by
  change projection (relationPolynomial "13,1,454,1;8,1,9,1,292,1") = 0
  exact csv_relation_zero _ relation976_mem
theorem relation977_mem : "17,1,382,1;8,1,518,1;0,4,645,1;0,4,644,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block8[26]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation977_zero : nativeImage "17,1,382,1;8,1,518,1;0,4,645,1;0,4,644,1" = 0 := by
  change projection (relationPolynomial "17,1,382,1;8,1,518,1;0,4,645,1;0,4,644,1") = 0
  exact csv_relation_zero _ relation977_mem
theorem relation978_mem : "19,1,347,1;16,1,382,1;14,1,436,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block9[12]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation978_zero : nativeImage "19,1,347,1;16,1,382,1;14,1,436,1" = 0 := by
  change projection (relationPolynomial "19,1,347,1;16,1,382,1;14,1,436,1") = 0
  exact csv_relation_zero _ relation978_mem
theorem relation979_mem : "49,1,218,1;39,1,258,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block12[20]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation979_zero : nativeImage "49,1,218,1;39,1,258,1" = 0 := by
  change projection (relationPolynomial "49,1,218,1;39,1,258,1") = 0
  exact csv_relation_zero _ relation979_mem
theorem relation980_mem : "39,1,258,1;31,1,277,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block12[21]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation980_zero : nativeImage "39,1,258,1;31,1,277,1" = 0 := by
  change projection (relationPolynomial "39,1,258,1;31,1,277,1") = 0
  exact csv_relation_zero _ relation980_mem
theorem relation981_mem : "31,1,277,1;19,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block12[22]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation981_zero : nativeImage "31,1,277,1;19,1,344,1" = 0 := by
  change projection (relationPolynomial "31,1,277,1;19,1,344,1") = 0
  exact csv_relation_zero _ relation981_mem
theorem relation982_mem : "19,1,344,1;9,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block12[23]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation982_zero : nativeImage "19,1,344,1;9,1,489,1" = 0 := by
  change projection (relationPolynomial "19,1,344,1;9,1,489,1") = 0
  exact csv_relation_zero _ relation982_mem
theorem relation983_mem : "9,1,489,1;8,1,16,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block12[24]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation983_zero : nativeImage "9,1,489,1;8,1,16,1,245,1" = 0 := by
  change projection (relationPolynomial "9,1,489,1;8,1,16,1,245,1") = 0
  exact csv_relation_zero _ relation983_mem
theorem relation984_mem : "18,1,377,1;1,2,660,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block16[19]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation984_zero : nativeImage "18,1,377,1;1,2,660,1" = 0 := by
  change projection (relationPolynomial "18,1,377,1;1,2,660,1") = 0
  exact csv_relation_zero _ relation984_mem
theorem relation985_mem : "69,1,181,1;18,1,376,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block16[23]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation985_zero : nativeImage "69,1,181,1;18,1,376,1" = 0 := by
  change projection (relationPolynomial "69,1,181,1;18,1,376,1") = 0
  exact csv_relation_zero _ relation985_mem
theorem relation986_mem : "3,1,620,1;1,1,680,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block19[2]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation986_zero : nativeImage "3,1,620,1;1,1,680,1" = 0 := by
  change projection (relationPolynomial "3,1,620,1;1,1,680,1") = 0
  exact csv_relation_zero _ relation986_mem
theorem relation987_mem : "17,1,414,1;16,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block19[25]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation987_zero : nativeImage "17,1,414,1;16,1,415,1" = 0 := by
  change projection (relationPolynomial "17,1,414,1;16,1,415,1") = 0
  exact csv_relation_zero _ relation987_mem
theorem relation988_mem : "23,1,332,1;13,1,476,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block19[27]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation988_zero : nativeImage "23,1,332,1;13,1,476,1" = 0 := by
  change projection (relationPolynomial "23,1,332,1;13,1,476,1") = 0
  exact csv_relation_zero _ relation988_mem
theorem relation989_mem : "16,1,415,1;8,1,534,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block19[30]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation989_zero : nativeImage "16,1,415,1;8,1,534,1" = 0 := by
  change projection (relationPolynomial "16,1,415,1;8,1,534,1") = 0
  exact csv_relation_zero _ relation989_mem
theorem relation990_mem : "23,1,331,1;13,1,474,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block20[29]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation990_zero : nativeImage "23,1,331,1;13,1,474,1" = 0 := by
  change projection (relationPolynomial "23,1,331,1;13,1,474,1") = 0
  exact csv_relation_zero _ relation990_mem
theorem relation991_mem : "24,1,328,1;13,1,473,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block24[11]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation991_zero : nativeImage "24,1,328,1;13,1,473,1" = 0 := by
  change projection (relationPolynomial "24,1,328,1;13,1,473,1") = 0
  exact csv_relation_zero _ relation991_mem
theorem relation992_mem : "23,1,328,1;13,1,472,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block25[11]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation992_zero : nativeImage "23,1,328,1;13,1,472,1" = 0 := by
  change projection (relationPolynomial "23,1,328,1;13,1,472,1") = 0
  exact csv_relation_zero _ relation992_mem
theorem relation993_mem : "17,1,20,1,188,1;15,1,422,1;8,1,530,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block28[27]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation993_zero : nativeImage "17,1,20,1,188,1;15,1,422,1;8,1,530,1" = 0 := by
  change projection (relationPolynomial "17,1,20,1,188,1;15,1,422,1;8,1,530,1") = 0
  exact csv_relation_zero _ relation993_mem
theorem relation994_mem : "15,1,422,1;2,1,654,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block28[30]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation994_zero : nativeImage "15,1,422,1;2,1,654,1" = 0 := by
  change projection (relationPolynomial "15,1,422,1;2,1,654,1") = 0
  exact csv_relation_zero _ relation994_mem
theorem relation995_mem : "2,1,654,1;0,5,646,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block29[0]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation995_zero : nativeImage "2,1,654,1;0,5,646,1" = 0 := by
  change projection (relationPolynomial "2,1,654,1;0,5,646,1") = 0
  exact csv_relation_zero _ relation995_mem
theorem relation996_mem : "113,1,138,1;30,1,292,1;16,1,404,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block30[28]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation996_zero : nativeImage "113,1,138,1;30,1,292,1;16,1,404,1" = 0 := by
  change projection (relationPolynomial "113,1,138,1;30,1,292,1;16,1,404,1") = 0
  exact csv_relation_zero _ relation996_mem
theorem relation997_mem : "30,1,292,1;10,1,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block30[29]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation997_zero : nativeImage "30,1,292,1;10,1,491,1" = 0 := by
  change projection (relationPolynomial "30,1,292,1;10,1,491,1") = 0
  exact csv_relation_zero _ relation997_mem
theorem relation998_mem : "16,1,404,1;8,1,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block30[30]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation998_zero : nativeImage "16,1,404,1;8,1,529,1" = 0 := by
  change projection (relationPolynomial "16,1,404,1;8,1,529,1") = 0
  exact csv_relation_zero _ relation998_mem
theorem relation999_mem : "10,1,491,1;0,1,17,1,380,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block30[31]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation999_zero : nativeImage "10,1,491,1;0,1,17,1,380,1" = 0 := by
  change projection (relationPolynomial "10,1,491,1;0,1,17,1,380,1") = 0
  exact csv_relation_zero _ relation999_mem
theorem relation1000_mem : "113,1,137,1;112,1,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block31[2]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1000_zero : nativeImage "113,1,137,1;112,1,138,1" = 0 := by
  change projection (relationPolynomial "113,1,137,1;112,1,138,1") = 0
  exact csv_relation_zero _ relation1000_mem
theorem relation1001_mem : "112,1,138,1;64,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 22 chunkBound rows transcription
    (block31[5]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1001_zero : nativeImage "112,1,138,1;64,1,185,1" = 0 := by
  change projection (relationPolynomial "112,1,138,1;64,1,185,1") = 0
  exact csv_relation_zero _ relation1001_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk022
